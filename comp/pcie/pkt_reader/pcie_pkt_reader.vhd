-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all;


-- =========================================================================
--  Basic description
-- =========================================================================
--
-- This module accepts request instructions to read data from a memory device over the PCIe.
-- The user provides the Address and Length of the requested data on the RX_USR interface.
-- They also provide an ID, which will identify the read data received on the TX_USR interface, which may arrive out of order.
--
-- This module's non-user interfaces (PCIE_UP, PCIE_DOWN) are compatible with the PTC module.
-- The transactions it receives from the PTC module may come in parts and mixed with parts from other read data.
-- However, the parts of one request will arrive in order.
-- This module pieces these parts together and marks them with the ID from the request instruction.
--
-- ..warning::
--
--   To ensure correct function, DO NOT reuse IDs until appropriate response is received!
--
-- Must still be tested in scenarios where:
--
--    #. requests generate multiple completions and
--    #. completions arrive out-of-order (in-order per same tag).
--
entity PCIE_PKT_READER is
    generic (
        -- =================================================================
        -- MFB parameters
        -- =================================================================

        -- Number of MFB Regions in a word, cannot handle more than 1.
        MFB_REGIONS     : natural := 1;
        MFB_REGION_SIZE : natural := 8;
        MFB_BLOCK_SIZE  : natural := 8;
        MFB_ITEM_WIDTH  : natural := 8;

        -- =================================================================
        -- Other parameters
        -- =================================================================

        -- Maximum packet size (in bytes).
        PKT_MTU         : natural := 2**12;
        -- Size of the Main Memory for responses, in number of stored MFB words.
        MEMORY_SIZE     : natural := 1024;
        ID_WIDTH        : natural := 11;
        PCIE_MRRS_WIDTH : natural := 13;
        -- Size of a RAM page (in bytes).
        PAGE_SIZE       : natural := 4096;
        DEVICE          : string := "AGILEX"
    );
    port (
        CLK                   : in std_logic;
        RESET                 : in std_logic;

        PCIE_MRRS             : in std_logic_vector(PCIE_MRRS_WIDTH-1 downto 0);

        -- =================================================================
        -- User Request Interface (instruction for which data to read)
        -- =================================================================

        USER_REQ_MVB_ID       : in  std_logic_vector(MFB_REGIONS*ID_WIDTH-1 downto 0);
        USER_REQ_MVB_ADDRESS  : in  std_logic_vector(MFB_REGIONS*DMA_REQUEST_GLOBAL_W-1 downto 0);
        USER_REQ_MVB_LENGTH   : in  std_logic_vector(MFB_REGIONS*log2(PKT_MTU+1)-1 downto 0);
        USER_REQ_MVB_VLD      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        USER_REQ_MVB_SRC_RDY  : in  std_logic;
        USER_REQ_MVB_DST_RDY  : out std_logic;

        -- =================================================================
        -- User Response Interface (read data with request's ID)
        -- =================================================================

        -- Requested data.
        USER_RESP_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- ID number that identifies the requested data, valid with SOF.
        USER_RESP_MFB_ID      : out std_logic_vector(MFB_REGIONS*ID_WIDTH-1 downto 0);
        USER_RESP_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        USER_RESP_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        USER_RESP_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        USER_RESP_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        USER_RESP_MFB_SRC_RDY : out std_logic;
        USER_RESP_MFB_DST_RDY : in  std_logic;

        -- =================================================================
        -- PCIE Up Interface (sends Read requests to PTC)
        -- =================================================================

        -- Contains DMA Upstream header
        PCIE_UP_MVB_DATA      : out std_logic_vector(MFB_REGIONS*DMA_UPHDR_WIDTH-1 downto 0);
        PCIE_UP_MVB_VLD       : out std_logic_vector(MFB_REGIONS-1 downto 0);
        PCIE_UP_MVB_SRC_RDY   : out std_logic;
        PCIE_UP_MVB_DST_RDY   : in  std_logic;

        -- =================================================================
        -- PCIE Down Interface (receives Read responses from PTC)
        -- =================================================================

        -- Contains DMA Downstream header
        PCIE_DOWN_MVB_DATA    : in  std_logic_vector(MFB_REGIONS*DMA_DOWNHDR_WIDTH-1 downto 0);
        PCIE_DOWN_MVB_VLD     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        PCIE_DOWN_MVB_SRC_RDY : in  std_logic;
        PCIE_DOWN_MVB_DST_RDY : out std_logic;

        PCIE_DOWN_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        PCIE_DOWN_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        PCIE_DOWN_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        PCIE_DOWN_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        PCIE_DOWN_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        PCIE_DOWN_MFB_SRC_RDY : in  std_logic;
        PCIE_DOWN_MFB_DST_RDY : out std_logic
    );
end entity;

architecture FULL of PCIE_PKT_READER is

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    constant REGION_WIDTH  : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant WORD_WIDTH    : natural := MFB_REGIONS*REGION_WIDTH;
    constant WORD_ITEMS    : natural := WORD_WIDTH/MFB_ITEM_WIDTH;
    constant SOF_POS_WIDTH : natural := max(1,log2(MFB_REGION_SIZE));
    constant EOF_POS_WIDTH : natural := max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));

    -- Main Memory read address (specifies a word within the memory).
    constant MM_RD_ADDR_W   : natural := log2(MEMORY_SIZE);
    -- Main Memory write address (specifies a word and a byte within the memory).
    constant MM_WR_ADDR_W   : natural := log2(MEMORY_SIZE) + log2(WORD_ITEMS);

    -- Width of Tag Memory data:         MM WR addr   + packet ID
    constant TAGMEM_DATA_W  : natural := MM_WR_ADDR_W + ID_WIDTH;
    -- Width of Tag Memory metadata:        (vld + TAGMEM_DATA , vld + cmpl + DMA_COMPLETION_LENGTH)
    constant TAGMEM_META_W  : natural := max(1   + TAGMEM_DATA_W, 1   + 1    + DMA_COMPLETION_LENGTH_W);
    -- Width of WR instr FIFO data:      vld + MM WR addr   + ID       + tag
    constant WR_INSTR_WIDTH : natural := 1   + MM_WR_ADDR_W + ID_WIDTH + DMA_REQUEST_TAG_W;
    -- Max number of words a packet (MTU) can stretch over.
    constant MAX_WORDS_W    : natural := log2(div_roundup(PKT_MTU,WORD_ITEMS));
    -- Width of ID Memory data:          MM RD addr     + words       + EOFPOS in word   + Tag count
    constant IDMEM_DATA_W   : natural := MM_RD_ADDR_W+1 + MAX_WORDS_W + log2(WORD_ITEMS) + DMA_REQUEST_TAG_W;
    -- Width of ID Memory metadata:      vld + IDMEM_DATA
    constant IDMEM_META_W   : natural := 1   + IDMEM_DATA_W;
    -- Width of RD instr FIFO data:      ID       + ID Mem data  - Tag count
    constant RD_INSTR_WIDTH : natural := ID_WIDTH + IDMEM_DATA_W - DMA_REQUEST_TAG_W;

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    signal idmem_wr_id              : std_logic_vector(MFB_REGIONS*ID_WIDTH-1 downto 0);
    signal idmem_wr_addr            : std_logic_vector(MFB_REGIONS*MM_RD_ADDR_W+1-1 downto 0);
    signal idmem_wr_words           : std_logic_vector(MFB_REGIONS*MAX_WORDS_W-1 downto 0);
    signal idmem_wr_eof_pos         : std_logic_vector(MFB_REGIONS*log2(WORD_ITEMS)-1 downto 0);
    signal idmem_wr_tag_cnt         : std_logic_vector(MFB_REGIONS*DMA_REQUEST_TAG_W-1 downto 0);
    signal idmem_wr_vld             : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal tagmem_wr_tag            : std_logic_vector(MFB_REGIONS*DMA_REQUEST_TAG_W-1 downto 0);
    signal tagmem_wr_addr           : std_logic_vector(MFB_REGIONS*MM_WR_ADDR_W-1 downto 0);
    signal tagmem_wr_id             : std_logic_vector(MFB_REGIONS*ID_WIDTH-1 downto 0);
    signal tagmem_wr_vld            : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal tagmem_free_tag          : std_logic_vector(MFB_REGIONS*DMA_REQUEST_TAG_W-1 downto 0);
    signal tagmem_free_vld          : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal mm_freed_rd_ptr          : std_logic_vector(MM_RD_ADDR_W+1-1 downto 0);

    signal tagmem_wr_addr_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(MM_WR_ADDR_W-1 downto 0);
    signal tagmem_wr_id_arr         : slv_array_t(MFB_REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal tagmem_wr0_meta_arr      : slv_array_t(MFB_REGIONS-1 downto 0)(TAGMEM_META_W-1 downto 0);
    signal tagmem_wr1_meta_arr      : slv_array_t(MFB_REGIONS-1 downto 0)(TAGMEM_META_W-1 downto 0);

    signal tagmem_wr_sel            : slv_array_t(2*MFB_REGIONS-1 downto 0)(DMA_REQUEST_TAG_W-1 downto 0);
    signal tagmem_wr_meta           : slv_array_t(2*MFB_REGIONS-1 downto 0)(TAGMEM_META_W-1 downto 0);

    signal tagmem_rd_sel            : slv_array_t(2*MFB_REGIONS-1 downto 0)(DMA_REQUEST_TAG_W-1 downto 0);
    signal tagmem_rd1_sel           : slv_array_t(MFB_REGIONS-1 downto 0)(DMA_REQUEST_TAG_W-1 downto 0);
    signal tagmem_rd_data           : slv_array_t(2*MFB_REGIONS-1 downto 0)(TAGMEM_DATA_W-1 downto 0);
    signal tagmem_rd_data_2d_arr    : slv_array_2d_t(2-1 downto 0)(MFB_REGIONS-1 downto 0)(TAGMEM_DATA_W-1 downto 0);
    signal tagmem_rd_meta           : slv_array_t(2*MFB_REGIONS-1 downto 0)(TAGMEM_META_W-1 downto 0);
    signal tagmem_rd_meta_2d_arr    : slv_array_2d_t(2-1 downto 0)(MFB_REGIONS-1 downto 0)(TAGMEM_META_W-1 downto 0);

    signal tagmem_wr0_new_data      : slv_array_t(MFB_REGIONS-1 downto 0)(TAGMEM_DATA_W-1 downto 0);
    signal tagmem_wr0_new_vld       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tagmem_wr0_cur_data      : slv_array_t(MFB_REGIONS-1 downto 0)(TAGMEM_DATA_W-1 downto 0);
    signal tagmem_wr0_data_arr      : slv_array_t(MFB_REGIONS-1 downto 0)(TAGMEM_DATA_W-1 downto 0);
    signal tagmem_wr1_resp_len      : u_array_t(MFB_REGIONS-1 downto 0)(DMA_COMPLETION_LENGTH_W+2-1 downto 0);
    signal tagmem_wr1_resp_cmpl     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tagmem_wr1_resp_vld      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tagmem_wr1_id            : slv_array_t(MFB_REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal tagmem_wr1_cur_addr      : slv_array_t(MFB_REGIONS-1 downto 0)(MM_WR_ADDR_W-1 downto 0);
    signal tagmem_wr1_new_addr      : slv_array_t(MFB_REGIONS-1 downto 0)(MM_WR_ADDR_W-1 downto 0);
    signal tagmem_wr1_upd_addr      : slv_array_t(MFB_REGIONS-1 downto 0)(MM_WR_ADDR_W-1 downto 0);
    signal tagmem_wr1_data_arr      : slv_array_t(MFB_REGIONS-1 downto 0)(TAGMEM_DATA_W-1 downto 0);
    signal tagmem_wr_data           : slv_array_t(2-1 downto 0)(MFB_REGIONS*TAGMEM_DATA_W-1 downto 0);

    signal idmem_wr_addr_arr        : slv_array_t(MFB_REGIONS-1 downto 0)(MM_RD_ADDR_W+1-1 downto 0);
    signal idmem_wr_words_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(MAX_WORDS_W-1 downto 0);
    signal idmem_wr_eof_pos_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(log2(WORD_ITEMS)-1 downto 0);
    signal idmem_wr_tag_cnt_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(DMA_REQUEST_TAG_W-1 downto 0);
    signal idmem_wr0_meta_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(IDMEM_META_W-1 downto 0);
    signal tagmem_tag_completed     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal idmem_wr1_meta_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(IDMEM_META_W-1 downto 0);

    signal idmem_wr_sel             : slv_array_t(2-1 downto 0)(MFB_REGIONS*ID_WIDTH-1 downto 0);
    signal idmem_wr_meta            : slv_array_t(2-1 downto 0)(MFB_REGIONS*IDMEM_META_W-1 downto 0);

    signal idmem_rd_sel             : slv_array_t(2*MFB_REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal idmem_rd_sel_2d_arr      : slv_array_2d_t(2-1 downto 0)(MFB_REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal idmem_rd_data            : slv_array_t(2*MFB_REGIONS-1 downto 0)(IDMEM_DATA_W-1 downto 0);
    signal idmem_rd_data_2d_arr     : slv_array_2d_t(2-1 downto 0)(MFB_REGIONS-1 downto 0)(IDMEM_DATA_W-1 downto 0);
    signal idmem_rd_meta            : slv_array_t(2*MFB_REGIONS-1 downto 0)(IDMEM_META_W-1 downto 0);
    signal idmem_rd_meta_2d_arr     : slv_array_2d_t(2-1 downto 0)(MFB_REGIONS-1 downto 0)(IDMEM_META_W-1 downto 0);

    signal idmem_wr0_new_data       : slv_array_t(MFB_REGIONS-1 downto 0)(IDMEM_DATA_W-1 downto 0);
    signal idmem_wr0_new_vld        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal idmem_wr0_cur_data       : slv_array_t(MFB_REGIONS-1 downto 0)(IDMEM_DATA_W-1 downto 0);
    signal idmem_wr0_data_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(IDMEM_DATA_W-1 downto 0);
    signal idmem_wr1_cur_tag_cnt    : slv_array_t(MFB_REGIONS-1 downto 0)(DMA_REQUEST_TAG_W-1 downto 0);
    signal idmem_wr1_dec_tag_cnt    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal idmem_wr1_new_tag_cnt    : slv_array_t(MFB_REGIONS-1 downto 0)(DMA_REQUEST_TAG_W-1 downto 0);
    signal idmem_wr1_upd_tag_cnt    : slv_array_t(MFB_REGIONS-1 downto 0)(DMA_REQUEST_TAG_W-1 downto 0);
    signal idmem_wr1_data_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(IDMEM_DATA_W-1 downto 0);
    signal idmem_wr_data            : slv_array_t(2-1 downto 0)(MFB_REGIONS*IDMEM_DATA_W-1 downto 0);

    signal pcie_down_mvb_data_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(DMA_DOWNHDR_WIDTH-1 downto 0);
    signal pcie_resp_len            : slv_array_t(MFB_REGIONS-1 downto 0)(DMA_COMPLETION_LENGTH_W-1 downto 0);
    signal pcie_resp_cmlp           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pcie_resp_tag            : slv_array_t(MFB_REGIONS-1 downto 0)(DMA_COMPLETION_TAG_W-1 downto 0);
    signal pcie_resp_vld            : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal wr_instr_fifo_di_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(WR_INSTR_WIDTH-1 downto 0);
    signal wr_instr_fifo_di         : std_logic_vector(MFB_REGIONS*WR_INSTR_WIDTH-1 downto 0);
    signal wr_instr_fifo_wr         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal wr_instr_fifo_full       : std_logic;
    signal wr_instr_fifo_do         : std_logic_vector(WR_INSTR_WIDTH-1 downto 0);
    signal wr_instr_fifo_rd         : std_logic_vector(1-1 downto 0);
    signal wr_instr_fifo_empty      : std_logic_vector(1-1 downto 0);

    signal wr_instr_addr_word       : unsigned(MM_RD_ADDR_W-1 downto 0);
    signal wr_instr_addr_byte       : std_logic_vector(log2(WORD_ITEMS)-1 downto 0);
    signal wr_instr_id              : std_logic_vector(ID_WIDTH-1 downto 0);
    signal wr_instr_tag             : std_logic_vector(DMA_REQUEST_TAG_W-1 downto 0);
    signal wr_instr_cmpl            : std_logic;

    signal pcie_mfb_fifo_data       : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal pcie_mfb_fifo_sof_pos    : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal pcie_mfb_fifo_eof_pos    : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal pcie_mfb_fifo_sof        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pcie_mfb_fifo_eof        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pcie_mfb_fifo_src_rdy    : std_logic;
    signal pcie_mfb_fifo_dst_rdy    : std_logic;

    signal pcie_axi_tdata           : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal pcie_axi_tkeep           : std_logic_vector(WORD_WIDTH/8-1 downto 0);
    signal pcie_axi_tlast           : std_logic;
    signal pcie_axi_tvalid          : std_logic;
    signal pcie_axi_tready          : std_logic;

    signal pkt_ended                : std_logic;
    signal pcie_axi_sof             : std_logic;

    signal bs_shift_reg             : std_logic_vector(log2(WORD_ITEMS)-1 downto 0);
    signal bs_item_vld              : std_logic_vector(WORD_ITEMS-1 downto 0);

    signal bs_shift                 : std_logic_vector(log2(WORD_ITEMS)-1 downto 0);
    signal bs_din                   : std_logic_vector(WORD_ITEMS*(MFB_ITEM_WIDTH+1)-1 downto 0);
    signal bs_ready                 : std_logic;
    signal bs_dout                  : std_logic_vector(WORD_ITEMS*(MFB_ITEM_WIDTH+1)-1 downto 0);

    signal bs_dout_arr              : slv_array_t(WORD_ITEMS-1 downto 0)(MFB_ITEM_WIDTH downto 0);
    signal bs_dout_data             : slv_array_t(WORD_ITEMS-1 downto 0)(MFB_ITEM_WIDTH-1 downto 0);
    signal bs_dout_vld              : std_logic_vector(WORD_ITEMS-1 downto 0);

    signal mm_wr_addr_curr          : unsigned(MM_RD_ADDR_W-1 downto 0);
    signal mm_wr_addr_next          : unsigned(MM_RD_ADDR_W-1 downto 0);


    signal ptr                      : integer range WORD_ITEMS-1 downto 0;

    signal mm_wr_data               : slv_array_t(WORD_ITEMS-1 downto 0)(MFB_ITEM_WIDTH-1 downto 0);
    signal mm_wr_addr               : slv_array_t(WORD_ITEMS-1 downto 0)(MM_RD_ADDR_W-1 downto 0);
    signal mm_wr_en                 : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal mm_rd_data               : slv_array_t(WORD_ITEMS-1 downto 0)(MFB_ITEM_WIDTH-1 downto 0);
    signal mm_rd_addr               : slv_array_t(WORD_ITEMS-1 downto 0)(MM_RD_ADDR_W-1 downto 0);
    signal mm_rd_pipe_en            : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal mm_rd_curr_addr          : std_logic_vector(MM_RD_ADDR_W-1 downto 0);

    signal transs_rx_trans_id       : slv_array_t(MFB_REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal transs_rx_trans_meta     : slv_array_t(MFB_REGIONS-1 downto 0)(MM_RD_ADDR_W+1-1 downto 0);
    signal transs_rx_trans_src_rdy  : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal transs_rx_conf_id        : slv_array_t(MFB_REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal transs_rx_conf_vld       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal transs_tx_id             : slv_array_t(MFB_REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal transs_tx_meta           : slv_array_t(MFB_REGIONS-1 downto 0)(MM_RD_ADDR_W+1-1 downto 0);
    signal transs_tx_src_rdy        : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal rd_instr_fifo_di_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(RD_INSTR_WIDTH-1 downto 0);
    signal rd_instr_fifo_di         : std_logic_vector(MFB_REGIONS*RD_INSTR_WIDTH-1 downto 0);
    signal rd_instr_fifo_wr         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rd_instr_fifo_full       : std_logic;
    signal rd_instr_fifo_do         : std_logic_vector(RD_INSTR_WIDTH-1 downto 0);
    signal rd_instr_fifo_rd         : std_logic_vector(1-1 downto 0);
    signal rd_instr_fifo_empty      : std_logic_vector(1-1 downto 0);
    signal rd_instr_invalidate      : std_logic;

    signal rd_instr_id              : std_logic_vector(ID_WIDTH-1 downto 0);
    signal rd_instr_addr            : std_logic_vector(MM_RD_ADDR_W+1-1 downto 0);
    signal rd_instr_words           : std_logic_vector(MAX_WORDS_W-1 downto 0);
    signal rd_instr_eofpos          : std_logic_vector(log2(WORD_ITEMS)-1 downto 0);
    signal rd_instr_vld_reg         : std_logic;

    signal rd_instr_id_reg          : std_logic_vector(ID_WIDTH-1 downto 0);
    signal rd_instr_addr_reg        : std_logic_vector(MM_RD_ADDR_W-1 downto 0);
    signal rd_instr_words_reg       : std_logic_vector(MAX_WORDS_W-1 downto 0);
    signal rd_instr_eofpos_reg      : std_logic_vector(log2(WORD_ITEMS)-1 downto 0);

    signal tx_mfb_id                : std_logic_vector(ID_WIDTH-1 downto 0);
    signal tx_mfb_eofpos            : std_logic_vector(EOF_POS_WIDTH-1 downto 0);
    signal rd_instr_new_loaded      : std_logic;
    signal tx_mfb_sof               : std_logic;
    signal tx_mfb_eof               : std_logic;
    signal tx_mfb_src_rdy           : std_logic;
    signal rd_instr_addr_cnt        : unsigned(MAX_WORDS_W-1 downto 0);
    signal reading_last_word        : std_logic;

begin

    assert MFB_REGIONS = 1
        report "PCIE_PKT_READER: unable to handle more than 1 MFB Region!"
        severity Failure;

    assert PKT_MTU < MEMORY_SIZE*WORD_ITEMS
        report "PCIE_PKT_READER: the value of MEMORY_SIZE is not large enough to fit even a single MTU-sized packet!"
        severity Failure;

    -- ========================================================
    --  Process user requests
    --   - break instructions according to PCIe spec and
    --     prepare records to manage responses
    -- ========================================================

    request_processor_i : entity work.PPR_REQUEST_PROCESSOR
    generic map (
        MVB_ITEMS         => MFB_REGIONS,
        PKT_MTU           => PKT_MTU,
        MEMORY_ITEMS      => MEMORY_SIZE,
        MEMORY_ITEM_WIDTH => WORD_WIDTH,
        ID_WIDTH          => ID_WIDTH,
        PCIE_MRRS_WIDTH   => PCIE_MRRS_WIDTH,
        PAGE_SIZE         => PAGE_SIZE,
        DEVICE            => DEVICE
    )
    port map (
        CLK               => CLK,
        RESET             => RESET,

        PCIE_MRRS         => PCIE_MRRS,

        RX_MVB_ID         => USER_REQ_MVB_ID,
        RX_MVB_ADDRESS    => USER_REQ_MVB_ADDRESS,
        RX_MVB_LENGTH     => USER_REQ_MVB_LENGTH,
        RX_MVB_VLD        => USER_REQ_MVB_VLD,
        RX_MVB_SRC_RDY    => USER_REQ_MVB_SRC_RDY,
        RX_MVB_DST_RDY    => USER_REQ_MVB_DST_RDY,

        TX_MVB_DATA       => PCIE_UP_MVB_DATA,
        TX_MVB_VLD        => PCIE_UP_MVB_VLD,
        TX_MVB_SRC_RDY    => PCIE_UP_MVB_SRC_RDY,
        TX_MVB_DST_RDY    => PCIE_UP_MVB_DST_RDY,

        IDMEM_ID          => idmem_wr_id,
        IDMEM_ADDR        => idmem_wr_addr,
        IDMEM_WORDS       => idmem_wr_words,
        IDMEM_EOF_POS     => idmem_wr_eof_pos,
        IDMEM_TAG_CNT     => idmem_wr_tag_cnt,
        IDMEM_VLD         => idmem_wr_vld,

        TAGMEM_TAG        => tagmem_wr_tag,
        TAGMEM_ADDR       => tagmem_wr_addr,
        TAGMEM_ID         => tagmem_wr_id,
        TAGMEM_VLD        => tagmem_wr_vld,

        TAGMEM_FREE_TAG   => tagmem_free_tag,
        TAGMEM_FREE_VLD   => tagmem_free_vld,

        MEM_RD_PTR        => mm_freed_rd_ptr
    );

    tagmem_free_tag <= wr_instr_tag;
    tagmem_free_vld <= tagmem_tag_completed;

    -- ========================================================
    --  Store records to manage responses
    -- ========================================================

    -- --------------------------------------------------------
    --  Tag record memory
    -- --------------------------------------------------------
    tagmem_wr_addr_arr <= slv_array_deser(tagmem_wr_addr, MFB_REGIONS);
    tagmem_wr_id_arr   <= slv_array_deser(tagmem_wr_id, MFB_REGIONS);
    tag_mem_wr0_g : for r in 0 to MFB_REGIONS-1 generate
        tagmem_wr0_meta_arr(r) <= tagmem_wr_vld(r) & tagmem_wr_addr_arr(r) & tagmem_wr_id_arr(r);
    end generate;

    tag_mem_wr1_g : for r in 0 to MFB_REGIONS-1 generate
        tagmem_wr1_meta_arr(r) <= (
            DMA_COMPLETION_COMPLETED_O+1 => pcie_resp_vld (r),
            DMA_COMPLETION_COMPLETED_O   => pcie_resp_cmlp(r),
            DMA_COMPLETION_LENGTH        => pcie_resp_len (r),
            others                       => '0');
    end generate;

    -- The thought here is to enable accessing this memory's contents from two sources at the same time:
    -- 1) Source 0: the Request Processor's TAGMEM interface - only (over)writes data
    tagmem_wr_sel (MFB_REGIONS-1 downto 0) <= slv_array_deser(tagmem_wr_tag, MFB_REGIONS);
    tagmem_wr_meta(MFB_REGIONS-1 downto 0) <= tagmem_wr0_meta_arr;

    -- 2) Source 1: the instructions from PCIe down headers (responses) - updates data (Main Memory address field)
    tagmem_wr_sel (2*MFB_REGIONS-1 downto MFB_REGIONS) <= pcie_resp_tag;
    tagmem_wr_meta(2*MFB_REGIONS-1 downto MFB_REGIONS) <= array_item_resize_l(tagmem_wr1_meta_arr, TAGMEM_META_W);

    tag_mem_i : entity work.N_LOOP_OP
    generic map (
        DATA_WIDTH     => TAGMEM_DATA_W,
        ITEMS          => 2**DMA_REQUEST_TAG_W, -- to store all Tags
        QUICK_RESET_EN => False,
        RESET_VAL      => 0,
        READ_PORTS     => 0,
        OPERATORS      => 2*MFB_REGIONS,
        OPERATIONS     => 1,
        META_WIDTH     => TAGMEM_META_W,
        USE_REG_ARRAY  => False,
        DEVICE         => DEVICE
    )
    port map (
        CLK           => CLK,
        RESET         => RESET,

        OP_ITEM_SEL   => tagmem_wr_sel,
        OP_OPERATIONS => (others => (others => '1')),
        OP_META       => tagmem_wr_meta,

        OP_IN_SEL     => tagmem_rd_sel,
        OP_IN_SRC     => open, -- use this to solve collisions when implementing support for MFB_REGIONS>1
        OP_IN_OPS     => open,
        OP_IN_DATA    => tagmem_rd_data,
        OP_IN_META    => tagmem_rd_meta,

        OP_OUT_DATA   => tagmem_wr_data,

        READ_ADDR     => (others => (others => '0')),
        READ_DATA     => open
    );

    tagmem_rd1_sel <= tagmem_rd_sel(2*MFB_REGIONS-1 downto MFB_REGIONS);

    tagmem_rd_data_2d_arr <= slv_array_2d_deser(slv_array_ser(tagmem_rd_data), 2, MFB_REGIONS);
    tagmem_rd_meta_2d_arr <= slv_array_2d_deser(slv_array_ser(tagmem_rd_meta), 2, MFB_REGIONS);

    -- Over write current data only when new data (from tagmem_rd_meta) are valid
    tagmem_wr0_data_g : for r in 0 to MFB_REGIONS-1 generate
        -- New data + valid from metadata (= new data from the TAGMEM Request Processor interface).
        tagmem_wr0_new_data(r) <= tagmem_rd_meta_2d_arr(0)(r)(TAGMEM_DATA_W-1 downto 0);
        tagmem_wr0_new_vld (r) <= tagmem_rd_meta_2d_arr(0)(r)(TAGMEM_DATA_W);
        -- Currently stored data
        tagmem_wr0_cur_data(r) <= tagmem_rd_data_2d_arr(0)(r);
        tagmem_wr0_data_arr(r) <= tagmem_wr0_new_data(r) when (tagmem_wr0_new_vld(r) = '1') else tagmem_wr0_cur_data(r);
    end generate;

    tagmem_wr1_data_g : for r in 0 to MFB_REGIONS-1 generate
        -- Length (Dwords->Bytes) + Completition bit + Valid bit from metadata (from MVB response header).
        tagmem_wr1_resp_len (r) <= resize_right(unsigned(tagmem_rd_meta_2d_arr(1)(r)(DMA_COMPLETION_LENGTH_W-1 downto 0)), DMA_COMPLETION_LENGTH_W+2);
        tagmem_wr1_resp_cmpl(r) <= tagmem_rd_meta_2d_arr(1)(r)(DMA_COMPLETION_LENGTH_W);
        tagmem_wr1_resp_vld (r) <= tagmem_rd_meta_2d_arr(1)(r)(DMA_COMPLETION_LENGTH_W+1);
        -- Packet ID - to associate update with correct record in the ID Mem
        tagmem_wr1_id       (r) <= tagmem_rd_data_2d_arr(1)(r)(ID_WIDTH-1 downto 0);
        -- Address from the current record - to be incremented by length of the incomming response.
        tagmem_wr1_cur_addr (r) <= tagmem_rd_data_2d_arr(1)(r)(TAGMEM_DATA_W-1 downto ID_WIDTH);
        tagmem_wr1_new_addr (r) <= std_logic_vector(unsigned(tagmem_wr1_cur_addr(r)) + tagmem_wr1_resp_len(r));
        tagmem_wr1_upd_addr (r) <= tagmem_wr1_new_addr(r) when (tagmem_wr1_resp_vld(r) = '1') else tagmem_wr1_cur_addr(r);
        tagmem_wr1_data_arr (r) <= tagmem_wr1_upd_addr(r) & tagmem_rd_data_2d_arr(1)(r)(ID_WIDTH-1 downto 0);
    end generate;

    tagmem_wr_data(  MFB_REGIONS-1 downto           0) <= tagmem_wr0_data_arr;
    tagmem_wr_data(2*MFB_REGIONS-1 downto MFB_REGIONS) <= tagmem_wr1_data_arr;

    -- --------------------------------------------------------
    --  ID record memory
    -- --------------------------------------------------------
    idmem_wr_addr_arr    <= slv_array_deser(idmem_wr_addr, MFB_REGIONS);
    idmem_wr_words_arr   <= slv_array_deser(idmem_wr_words, MFB_REGIONS);
    idmem_wr_eof_pos_arr <= slv_array_deser(idmem_wr_eof_pos, MFB_REGIONS);
    idmem_wr_tag_cnt_arr <= slv_array_deser(idmem_wr_tag_cnt, MFB_REGIONS);
    idmem_wr0_g : for r in 0 to MFB_REGIONS-1 generate
        idmem_wr0_meta_arr(r) <= idmem_wr_vld(r) & idmem_wr_addr_arr(r) & idmem_wr_words_arr(r) & idmem_wr_eof_pos_arr(r) & idmem_wr_tag_cnt_arr(r);
    end generate;

    -- Tag completed bit
    tagmem_tag_completed <= (others => wr_instr_cmpl and wr_instr_fifo_rd(0));
    idmem_wr1_g : for r in 0 to MFB_REGIONS-1 generate
        idmem_wr1_meta_arr(r) <= (0 => tagmem_tag_completed(r), others => '0');
    end generate;

    -- Like with Tag Mem - enable accessing this memory's contents from two sources at the same time:
    -- 1) Source 0: the Request Processor's IDMEM interface - only (over)writes data
    idmem_wr_sel (MFB_REGIONS-1 downto 0) <= slv_array_deser(idmem_wr_id, MFB_REGIONS);
    idmem_wr_meta(MFB_REGIONS-1 downto 0) <= idmem_wr0_meta_arr;

    -- 2) Source 1: tag completion updates from Tag Mem (passed through WR Instr FIFO to sync with the data).
    idmem_wr_sel (2*MFB_REGIONS-1 downto MFB_REGIONS) <= (others => wr_instr_id);
    idmem_wr_meta(2*MFB_REGIONS-1 downto MFB_REGIONS) <= idmem_wr1_meta_arr;

    id_mem_i : entity work.N_LOOP_OP
    generic map (
        DATA_WIDTH     => IDMEM_DATA_W,
        ITEMS          => 2**ID_WIDTH,
        QUICK_RESET_EN => False,
        RESET_VAL      => 0,
        READ_PORTS     => 0,
        OPERATORS      => 2*MFB_REGIONS,
        OPERATIONS     => 1,
        META_WIDTH     => IDMEM_META_W,
        USE_REG_ARRAY  => False,
        DEVICE         => DEVICE
    )
    port map (
        CLK           => CLK,
        RESET         => RESET,

        OP_ITEM_SEL   => idmem_wr_sel,
        OP_OPERATIONS => (others => (others => '1')),
        OP_META       => idmem_wr_meta,

        OP_IN_SEL     => idmem_rd_sel,
        OP_IN_SRC     => open, -- will need to use this to solve collisions when implementing support for MFB_REGIONS>1
        OP_IN_OPS     => open,
        OP_IN_DATA    => idmem_rd_data,
        OP_IN_META    => idmem_rd_meta,

        OP_OUT_DATA   => idmem_wr_data,

        READ_ADDR     => (others => (others => '0')),
        READ_DATA     => open
    );

    idmem_rd_sel_2d_arr  <= slv_array_2d_deser(slv_array_ser(idmem_rd_sel), 2, MFB_REGIONS);
    idmem_rd_data_2d_arr <= slv_array_2d_deser(slv_array_ser(idmem_rd_data), 2, MFB_REGIONS);
    idmem_rd_meta_2d_arr <= slv_array_2d_deser(slv_array_ser(idmem_rd_meta), 2, MFB_REGIONS);

    -- Over write current data only when new data (from idmem_rd_meta) are valid
    idmem_wr_data0_g : for r in 0 to MFB_REGIONS-1 generate
        -- New data + valid from metadata (= new data from the IDMEM Request Processor interface).
        idmem_wr0_new_data(r) <= idmem_rd_meta_2d_arr(0)(r)(IDMEM_DATA_W-1 downto 0);
        idmem_wr0_new_vld (r) <= idmem_rd_meta_2d_arr(0)(r)(IDMEM_DATA_W);
        -- Currently stored data
        idmem_wr0_cur_data(r) <= idmem_rd_data_2d_arr(0)(r);
        idmem_wr0_data_arr(r) <= idmem_wr0_new_data(r) when (idmem_wr0_new_vld(r) = '1') else idmem_wr0_cur_data(r);
    end generate;

    idmem_wr_data1_g : for r in 0 to MFB_REGIONS-1 generate
        -- Current value of tag count
        idmem_wr1_cur_tag_cnt(r) <= idmem_rd_data_2d_arr(1)(r)(DMA_REQUEST_TAG_W-1 downto 0);
        -- Decrement enable - when a Tag has been completed
        idmem_wr1_dec_tag_cnt(r) <= idmem_rd_meta_2d_arr(1)(r)(0);
        -- Decremented tag count
        idmem_wr1_new_tag_cnt(r) <= std_logic_vector(unsigned(idmem_wr1_cur_tag_cnt(r)) - 1);
        idmem_wr1_upd_tag_cnt(r) <= idmem_wr1_new_tag_cnt(r) when (idmem_wr1_dec_tag_cnt(r) = '1') else idmem_wr1_cur_tag_cnt(r);
        idmem_wr1_data_arr   (r) <= idmem_rd_data_2d_arr(1)(r)(IDMEM_DATA_W-1 downto DMA_REQUEST_TAG_W) & idmem_wr1_upd_tag_cnt(r);
    end generate;

    idmem_wr_data(  MFB_REGIONS-1 downto           0) <= idmem_wr0_data_arr;
    idmem_wr_data(2*MFB_REGIONS-1 downto MFB_REGIONS) <= idmem_wr1_data_arr;

    -- ========================================================
    --  Process responses and sends them to the Main Memory
    -- ========================================================

    -- --------------------------------------------------------
    --  MVB path
    -- --------------------------------------------------------
    PCIE_DOWN_MVB_DST_RDY <= not wr_instr_fifo_full and not rd_instr_fifo_full;

    -- Data from MVB headers are used to access records in the Tag Mem
    pcie_down_mvb_data_arr <= slv_array_deser(PCIE_DOWN_MVB_DATA, MFB_REGIONS);
    pcie_resp_instr_g : for r in 0 to MFB_REGIONS-1 generate
        pcie_resp_len (r) <= pcie_down_mvb_data_arr(r)(DMA_COMPLETION_LENGTH);
        pcie_resp_cmlp(r) <= pcie_down_mvb_data_arr(r)(DMA_COMPLETION_COMPLETED_O);
        pcie_resp_tag (r) <= pcie_down_mvb_data_arr(r)(DMA_COMPLETION_TAG);
    end generate;

    pcie_resp_vld <= PCIE_DOWN_MVB_VLD and PCIE_DOWN_MVB_SRC_RDY and PCIE_DOWN_MVB_DST_RDY;

    wr_instr_fifo_di_g : for r in 0 to MFB_REGIONS-1 generate
        wr_instr_fifo_di_arr(r) <= tagmem_wr1_resp_cmpl(r) & tagmem_wr1_cur_addr(r) & tagmem_wr1_id(r) & tagmem_rd1_sel(r);
    end generate;

    -- Store write instructions (only the WR address) from the record in the Tag Mem
    wr_instr_fifo_di <= slv_array_ser(wr_instr_fifo_di_arr);
    wr_instr_fifo_wr <= tagmem_wr1_resp_vld;

    wr_instr_fifo_i : entity work.FIFOX_MULTI
    generic map (
        DATA_WIDTH          => WR_INSTR_WIDTH,
        ITEMS               => 512,
        WRITE_PORTS         => MFB_REGIONS,
        READ_PORTS          => 1,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 0,
        ALMOST_EMPTY_OFFSET => 0,
        ALLOW_SINGLE_FIFO   => True,
        SAFE_READ_MODE      => False
    )
    port map (
        CLK    => CLK,
        RESET  => RESET,

        DI     => wr_instr_fifo_di,
        WR     => wr_instr_fifo_wr,
        FULL   => wr_instr_fifo_full, -- may need to use afull and stop PCIE_DOWN pipeline
        AFULL  => open,

        DO     => wr_instr_fifo_do,
        RD     => wr_instr_fifo_rd,
        EMPTY  => wr_instr_fifo_empty,
        AEMPTY => open
    );

    -- Read with valid SOF
    wr_instr_fifo_rd <= not wr_instr_fifo_empty and pcie_axi_tlast and pcie_axi_tvalid and pcie_axi_tready;

    -- Top bits address the word within the Main Memory -> used as the actual MM WR address.
    wr_instr_addr_word <= unsigned(wr_instr_fifo_do(WR_INSTR_WIDTH-1-1 downto WR_INSTR_WIDTH-1-log2(MEMORY_SIZE)));
    -- Bottom bits address the byte within the word -> used to rotate written data for proper alignment.
    wr_instr_addr_byte <= wr_instr_fifo_do(WR_INSTR_WIDTH-1-log2(MEMORY_SIZE)-1 downto WR_INSTR_WIDTH-1-MM_WR_ADDR_W);

    -- Packet ID to associate the instruction with the appropriate record in the ID Mem.
    wr_instr_id   <= wr_instr_fifo_do(ID_WIDTH+DMA_REQUEST_TAG_W-1 downto DMA_REQUEST_TAG_W);
    -- Completed tag number to return for reuse.
    wr_instr_tag  <= wr_instr_fifo_do(DMA_REQUEST_TAG_W-1 downto 0);
    -- Instruction (PCIe response) is the last one for this Tag -> update record in the ID Mem.
    wr_instr_cmpl <= wr_instr_fifo_do(WR_INSTR_WIDTH-1);

    -- --------------------------------------------------------
    --  Store response packets
    -- --------------------------------------------------------
    mfb_fifox_i : entity work.MFB_FIFOX
    generic map (
        REGIONS             => MFB_REGIONS,
        REGION_SIZE         => MFB_REGION_SIZE,
        BLOCK_SIZE          => MFB_BLOCK_SIZE,
        ITEM_WIDTH          => MFB_ITEM_WIDTH,
        META_WIDTH          => 0,
        FIFO_DEPTH          => 512,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 0,
        ALMOST_EMPTY_OFFSET => 0
    )
    port map (
        CLK         => CLK,
        RST         => RESET,

        RX_DATA     => PCIE_DOWN_MFB_DATA,
        RX_META     => (others => '0'),
        RX_SOF_POS  => PCIE_DOWN_MFB_SOF_POS,
        RX_EOF_POS  => PCIE_DOWN_MFB_EOF_POS,
        RX_SOF      => PCIE_DOWN_MFB_SOF,
        RX_EOF      => PCIE_DOWN_MFB_EOF,
        RX_SRC_RDY  => PCIE_DOWN_MFB_SRC_RDY,
        RX_DST_RDY  => PCIE_DOWN_MFB_DST_RDY,

        TX_DATA     => pcie_mfb_fifo_data,
        TX_META     => open,
        TX_SOF_POS  => pcie_mfb_fifo_sof_pos,
        TX_EOF_POS  => pcie_mfb_fifo_eof_pos,
        TX_SOF      => pcie_mfb_fifo_sof,
        TX_EOF      => pcie_mfb_fifo_eof,
        TX_SRC_RDY  => pcie_mfb_fifo_src_rdy,
        TX_DST_RDY  => pcie_mfb_fifo_dst_rdy,

        FIFO_STATUS => open,
        FIFO_AFULL  => open,
        FIFO_AEMPTY => open
    );

    -- --------------------------------------------------------
    --  Use MFB2AXI and AXI2MFB to convert bus to one
    --  MFB Region and only one packet per word.
    -- --------------------------------------------------------
    mfb2axi_i : entity work.MFB2AXI
    generic map (
        USE_IN_PIPE    => False,
        USE_OUT_PIPE   => False,
        REGIONS        => MFB_REGIONS,
        REGION_SIZE    => MFB_REGION_SIZE,
        BLOCK_SIZE     => MFB_BLOCK_SIZE,
        ITEM_WIDTH     => MFB_ITEM_WIDTH,
        AXI_DATA_WIDTH => REGION_WIDTH,
        PIPE_TYPE      => "SHREG",
        DEVICE         => DEVICE
    )
    port map (
        CLK            => CLK,
        RST            => RESET,

        RX_MFB_DATA    => pcie_mfb_fifo_data,
        RX_MFB_SOF_POS => pcie_mfb_fifo_sof_pos,
        RX_MFB_EOF_POS => pcie_mfb_fifo_eof_pos,
        RX_MFB_SOF     => pcie_mfb_fifo_sof,
        RX_MFB_EOF     => pcie_mfb_fifo_eof,
        RX_MFB_SRC_RDY => pcie_mfb_fifo_src_rdy,
        RX_MFB_DST_RDY => pcie_mfb_fifo_dst_rdy,

        TX_AXI_TDATA   => pcie_axi_tdata,
        TX_AXI_TKEEP   => pcie_axi_tkeep,
        TX_AXI_TLAST   => pcie_axi_tlast,
        TX_AXI_TVALID  => pcie_axi_tvalid,
        TX_AXI_TREADY  => pcie_axi_tready
    );

    pcie_axi_tready <= bs_ready and not wr_instr_fifo_empty(0);

    -- --------------------------------------------------------
    --  Detect SOF
    -- --------------------------------------------------------
    process (CLK)
    begin
        if rising_edge(CLK) then
            if ((pcie_axi_tvalid = '1') and (pcie_axi_tready = '1')) then
                pkt_ended <= '0';
            end if;
            if ((RESET = '1') or ((pcie_axi_tlast = '1') and (pcie_axi_tvalid = '1') and (pcie_axi_tready = '1'))) then
                pkt_ended <= '1';
            end if;
        end if;
    end process;

    pcie_axi_sof <= pkt_ended and pcie_axi_tvalid and pcie_axi_tready;

    -- --------------------------------------------------------
    --  Rotate data word to write MFB Items to the correct places within each word of the MM
    -- --------------------------------------------------------
    process (CLK)
    begin
        if rising_edge(CLK) then
            bs_shift_reg <= bs_shift;
        end if;
    end process;

    -- Validates Items of the current packet until EOF, used as WR Enable for the MM.
    bs_item_vld <= pcie_axi_tkeep and pcie_axi_tvalid and pcie_axi_tready;

    bs_din   <= slv_array_ser(concat_arr(slv_array_deser(pcie_axi_tdata, WORD_ITEMS), bs_item_vld));
    bs_shift <= wr_instr_addr_byte when (pcie_axi_sof = '1') else bs_shift_reg;

    barrel_shifter_i : entity work.BARREL_SHIFTER_GEN_PIPED
    generic map (
        BLOCKS            => WORD_ITEMS,
        BLOCK_WIDTH       => MFB_ITEM_WIDTH+1,
        BAR_SHIFT_LATENCY => 0,
        INPUT_REG         => False,
        OUTPUT_REG        => True,
        SHIFT_LEFT        => True, -- rotate UP to higher bits
        METADATA_WIDTH    => 0
    )
    port map (
        CLK         => CLK,
        RESET       => RESET,

        RX_DATA     => bs_din,
        RX_SEL      => bs_shift,
        RX_METADATA => (others => '0'),
        RX_SRC_RDY  => '1',
        RX_DST_RDY  => bs_ready,

        TX_DATA     => bs_dout,
        TX_METADATA => open,
        TX_SRC_RDY  => open,
        TX_DST_RDY  => not rd_instr_fifo_full
    );

    bs_dout_arr <= slv_array_deser(bs_dout, WORD_ITEMS);
    bs_output_g : for i in 0 to WORD_ITEMS-1 generate
        bs_dout_data(i) <= bs_dout_arr(i)(MFB_ITEM_WIDTH-1 downto 0);
        bs_dout_vld (i) <= bs_dout_arr(i)(MFB_ITEM_WIDTH);
    end generate;

    -- ========================================================
    --  The Main Memory (MM)
    --    - stores the partial responses from PCIe
    --      => completes packets for the user
    -- ========================================================

    -- --------------------------------------------------------
    --  WR Instr FIFO pre-read register
    -- --------------------------------------------------------
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (pcie_axi_sof = '1') then
                mm_wr_addr_curr <= wr_instr_addr_word;
                mm_wr_addr_next <= wr_instr_addr_word + 1;
            elsif (or bs_dout_vld = '1') then
                -- address the next word in the MM
                mm_wr_addr_curr <= mm_wr_addr_next;
                mm_wr_addr_next <= mm_wr_addr_next + 1;
            end if;
        end if;
    end process;

    ptr <= to_integer(unsigned(bs_shift_reg));
    mm_wr_addr_g : for i in 0 to WORD_ITEMS-1 generate
        mm_wr_addr(i) <= std_logic_vector(mm_wr_addr_next) when (i < ptr) else std_logic_vector(mm_wr_addr_curr);
    end generate;

    mm_wr_data <= bs_dout_data;
    mm_wr_en   <= bs_dout_vld;

    main_memory_g : for wi in 0 to WORD_ITEMS-1 generate
        main_memory_i : entity work.SDP_MEMX
        generic map (
            DATA_WIDTH     => MFB_ITEM_WIDTH,
            ITEMS          => MEMORY_SIZE,
            RAM_TYPE       => "AUTO",
            DEVICE         => DEVICE,
            OUTPUT_REG     => False -- False = 1 default reg, True = 2 regs
        )
        port map (
            CLK        => CLK,
            RESET      => RESET,

            WR_DATA    => mm_wr_data   (wi),
            WR_ADDR    => mm_wr_addr   (wi),
            WR_EN      => mm_wr_en     (wi),

            RD_DATA    => mm_rd_data   (wi),
            RD_ADDR    => mm_rd_addr   (wi),
            RD_PIPE_EN => mm_rd_pipe_en(wi)
        );
    end generate;

    mm_rd_pipe_en <= (others => USER_RESP_MFB_DST_RDY);
    mm_rd_addr    <= (others => mm_rd_curr_addr);

    mm_rd_curr_addr <= std_logic_vector(unsigned(rd_instr_addr_reg) + rd_instr_addr_cnt);

    -- ========================================================
    --  Read completed packets
    -- ========================================================

    rd_instr_fifo_g : for r in 0 to MFB_REGIONS-1 generate
        -- Write the ID Mem's record data to the RD Instr FIFO when completion of the last Tag arrives.
        rd_instr_fifo_wr    (r) <= idmem_wr1_dec_tag_cnt(r) when (unsigned(idmem_wr1_cur_tag_cnt(r)) = 1) else '0';
        -- All ID Mem data including the ID (the select signal) except tag count.
        rd_instr_fifo_di_arr(r) <= idmem_rd_sel_2d_arr(1)(r) & idmem_rd_data_2d_arr(1)(r)(IDMEM_DATA_W-1 downto DMA_REQUEST_TAG_W);
    end generate;
    rd_instr_fifo_di <= slv_array_ser(rd_instr_fifo_di_arr);

    -- Store read instructions
    rd_instr_fifo_i : entity work.FIFOX_MULTI
    generic map (
        DATA_WIDTH          => RD_INSTR_WIDTH,
        ITEMS               => 64,
        WRITE_PORTS         => MFB_REGIONS,
        READ_PORTS          => 1,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 0,
        ALMOST_EMPTY_OFFSET => 0,
        ALLOW_SINGLE_FIFO   => True,
        SAFE_READ_MODE      => False
    )
    port map (
        CLK    => CLK,
        RESET  => RESET,

        DI     => rd_instr_fifo_di,
        WR     => rd_instr_fifo_wr,
        FULL   => rd_instr_fifo_full, -- may need to use afull and stop PCIE_DOWN pipeline
        AFULL  => open,

        DO     => rd_instr_fifo_do,
        RD     => rd_instr_fifo_rd,
        EMPTY  => rd_instr_fifo_empty,
        AEMPTY => open
    );

    -- Read one at a time
    rd_instr_fifo_rd(0) <= not rd_instr_fifo_empty(0) and USER_RESP_MFB_DST_RDY and (not rd_instr_vld_reg or reading_last_word);

    (rd_instr_id, rd_instr_addr, rd_instr_words, rd_instr_eofpos) <= rd_instr_fifo_do;

    rd_instr_invalidate <= rd_instr_fifo_empty(0) and reading_last_word and USER_RESP_MFB_DST_RDY;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (rd_instr_fifo_rd(0) = '1') then
                rd_instr_id_reg     <= rd_instr_id;
                rd_instr_addr_reg   <= rd_instr_addr(MM_RD_ADDR_W-1 downto 0);
                rd_instr_words_reg  <= rd_instr_words;
                rd_instr_eofpos_reg <= rd_instr_eofpos;
                rd_instr_vld_reg    <= '1';
            end if;
            if ((RESET = '1') or (rd_instr_invalidate = '1')) then
                rd_instr_vld_reg <= '0';
            end if;
        end if;
    end process;

    -- Delay RD instruction data to match the 1 clock cycle latency of SDP_MEMX.
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (USER_RESP_MFB_DST_RDY = '1') then
                tx_mfb_id           <= rd_instr_id_reg;
                tx_mfb_eofpos       <= rd_instr_eofpos_reg(EOF_POS_WIDTH-1 downto 0);
                rd_instr_new_loaded <= rd_instr_fifo_rd(0); -- Loading a new RD instruction will result ...
                tx_mfb_sof          <= rd_instr_new_loaded; -- ... in a new packet (SOF) in the next clock cycle.
                tx_mfb_eof          <= reading_last_word;
                tx_mfb_src_rdy      <= rd_instr_vld_reg;
            end if;
            if (RESET = '1') then
                tx_mfb_src_rdy <= '0';
            end if;
        end if;
    end process;

    -- The counter updates the instruction's RD address with each read word.
    -- Respects the 1 clock cycle latency of SDP_MEMX.
    process (CLK)
    begin
        if rising_edge(CLK) then
            if ((USER_RESP_MFB_DST_RDY = '1') and (rd_instr_vld_reg = '1')) then
                rd_instr_addr_cnt <= rd_instr_addr_cnt + 1;
            end if;
            if ((RESET = '1') or ((reading_last_word = '1') and (USER_RESP_MFB_DST_RDY = '1'))) then
                rd_instr_addr_cnt <= (others => '0');
            end if;
        end if;
    end process;

    reading_last_word <= '1' when (rd_instr_addr_cnt+1 = unsigned(rd_instr_words_reg)) else '0';

    USER_RESP_MFB_DATA    <= slv_array_ser(mm_rd_data);
    USER_RESP_MFB_ID      <= tx_mfb_id;
    USER_RESP_MFB_SOF     <= (others => tx_mfb_sof);
    USER_RESP_MFB_EOF     <= (others => tx_mfb_eof);
    USER_RESP_MFB_SOF_POS <= (others => '0');
    USER_RESP_MFB_EOF_POS <= tx_mfb_eofpos;
    USER_RESP_MFB_SRC_RDY <= tx_mfb_src_rdy;

    -- ========================================================
    --  Read address freeing
    -- ========================================================

    transs_rx_trans_id      <= slv_array_deser(idmem_wr_id, MFB_REGIONS);
    transs_rx_trans_meta    <= slv_array_deser(idmem_wr_addr, MFB_REGIONS);
    transs_rx_trans_src_rdy <= idmem_wr_vld;

    transs_rx_conf_id  <= (others => rd_instr_id);
    transs_rx_conf_vld <= rd_instr_fifo_rd;

    trans_sorter_i : entity work.TRANS_SORTER
    generic map (
        RX_TRANSS           => MFB_REGIONS,
        TX_TRANSS           => MFB_REGIONS,
        ID_CONFS            => MFB_REGIONS,
        ID_WIDTH            => ID_WIDTH,
        TRANS_FIFO_ITEMS    => 2**ID_WIDTH, -- enough for RX_TRANS_DST_RDY and/or TRANS_FIFO_AFULL to never fire
        METADATA_WIDTH      => MM_RD_ADDR_W+1,
        MSIDT_BEHAV         => 0,
        MAX_SAME_ID_TRANS   => 0,
        USE_SHAKEDOWN_FIFOX => False,
        ALMOST_FULL_OFFSET  => 0,
        DEVICE              => DEVICE
    )
    port map (
        CLK              => CLK,
        RESET            => RESET,

        RX_TRANS_ID      => transs_rx_trans_id,
        RX_TRANS_META    => transs_rx_trans_meta,
        RX_TRANS_SRC_RDY => transs_rx_trans_src_rdy,
        RX_TRANS_DST_RDY => open,

        TRANS_FIFO_AFULL => open,

        RX_CONF_ID       => transs_rx_conf_id,
        RX_CONF_VLD      => transs_rx_conf_vld,

        TX_TRANS_ID      => open,
        TX_TRANS_META    => transs_tx_meta,
        TX_TRANS_SRC_RDY => transs_tx_src_rdy,
        TX_TRANS_DST_RDY => '1'
    );

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (transs_tx_src_rdy(0) = '1') then
                mm_freed_rd_ptr <= transs_tx_meta(0);
            end if;
            if (RESET = '1') then
                mm_freed_rd_ptr <= (others => '0');
            end if;
        end if;
    end process;

end architecture;
