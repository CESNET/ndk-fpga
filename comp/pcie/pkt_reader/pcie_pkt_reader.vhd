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
-- They also provide an ID, which will identify the read data received on the TX_USR interface.
-- The read data can be output in the same order as the requests were received when RESP_IN_ORDER=True.
-- When RESP_IN_ORDER=False, completed packets are output immediately regardless of request order.
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
entity PCIE_PKT_READER is
    generic (
        -- =================================================================
        -- MFB parameters
        -- =================================================================

        -- USER side.
        -- Number of MFB Regions in a word, cannot handle more than 1.
        REGIONS               : natural := 1;
        REGION_SIZE           : natural := 8;
        BLOCK_SIZE            : natural := 8;
        ITEM_WIDTH            : natural := 8;

        -- PCIE side.
        -- Number of DMA headers (MVB Items) in an upstream word.
        PCIE_UP_REGIONS       : natural := 2;
        -- Number of DMA headers and packets in a downstream word.
        PCIE_DOWN_REGIONS     : natural := 2;
        PCIE_DOWN_REGION_SIZE : natural := 1;
        PCIE_DOWN_BLOCK_SIZE  : natural := 8;
        PCIE_DOWN_ITEM_WIDTH  : natural := 32;

        -- =================================================================
        -- Other parameters
        -- =================================================================

        -- Maximum packet size (in bytes).
        PKT_MTU               : natural := 2**12;
        -- Size of the Main Memory for responses, in number of stored MFB words.
        MEMORY_SIZE           : natural := 1024;
        ID_WIDTH              : natural := 11;
        PCIE_MRRS_WIDTH       : natural := 12;
        -- Size of a RAM page (in bytes).
        PAGE_SIZE             : natural := 4096;
        -- When True, packets are output in the same order as the original requests.
        -- May lead to higher latency due to the reordering process.
        -- When False, completed packets are output immediately regardless of request order.
        RESP_IN_ORDER         : boolean := True;
        DEVICE                : string := "AGILEX"
    );
    port (
        CLK                   : in std_logic;
        RESET                 : in std_logic;

        PCIE_MRRS             : in std_logic_vector(PCIE_MRRS_WIDTH-1 downto 0);

        -- =================================================================
        -- User Request Interface (instruction for which data to read)
        -- =================================================================

        USER_REQ_MVB_ID       : in  std_logic_vector(REGIONS*ID_WIDTH-1 downto 0);
        USER_REQ_MVB_ADDRESS  : in  std_logic_vector(REGIONS*DMA_REQUEST_GLOBAL_W-1 downto 0);
        USER_REQ_MVB_LENGTH   : in  std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
        USER_REQ_MVB_VLD      : in  std_logic_vector(REGIONS-1 downto 0);
        USER_REQ_MVB_SRC_RDY  : in  std_logic;
        USER_REQ_MVB_DST_RDY  : out std_logic;

        -- =================================================================
        -- User Response Interface (read data with request's ID)
        -- =================================================================

        -- Requested data.
        USER_RESP_MFB_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        -- ID number that identifies the requested data, valid with SOF.
        USER_RESP_MFB_ID      : out std_logic_vector(REGIONS*ID_WIDTH-1 downto 0);
        USER_RESP_MFB_SOF     : out std_logic_vector(REGIONS-1 downto 0);
        USER_RESP_MFB_EOF     : out std_logic_vector(REGIONS-1 downto 0);
        USER_RESP_MFB_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        USER_RESP_MFB_EOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        USER_RESP_MFB_SRC_RDY : out std_logic;
        USER_RESP_MFB_DST_RDY : in  std_logic;

        -- =================================================================
        -- PCIE Up Interface (sends Read requests to PTC)
        -- =================================================================

        -- Contains DMA Upstream header
        PCIE_UP_MVB_DATA      : out std_logic_vector(PCIE_UP_REGIONS*DMA_UPHDR_WIDTH-1 downto 0);
        PCIE_UP_MVB_VLD       : out std_logic_vector(PCIE_UP_REGIONS-1 downto 0);
        PCIE_UP_MVB_SRC_RDY   : out std_logic;
        PCIE_UP_MVB_DST_RDY   : in  std_logic;

        -- =================================================================
        -- PCIE Down Interface (receives Read responses from PTC)
        -- =================================================================

        -- Contains DMA Downstream header
        PCIE_DOWN_MVB_DATA    : in  std_logic_vector(PCIE_DOWN_REGIONS*DMA_DOWNHDR_WIDTH-1 downto 0);
        PCIE_DOWN_MVB_VLD     : in  std_logic_vector(PCIE_DOWN_REGIONS-1 downto 0);
        PCIE_DOWN_MVB_SRC_RDY : in  std_logic;
        PCIE_DOWN_MVB_DST_RDY : out std_logic;

        PCIE_DOWN_MFB_DATA    : in  std_logic_vector(PCIE_DOWN_REGIONS*PCIE_DOWN_REGION_SIZE*PCIE_DOWN_BLOCK_SIZE*PCIE_DOWN_ITEM_WIDTH-1 downto 0);
        PCIE_DOWN_MFB_SOF     : in  std_logic_vector(PCIE_DOWN_REGIONS-1 downto 0);
        PCIE_DOWN_MFB_EOF     : in  std_logic_vector(PCIE_DOWN_REGIONS-1 downto 0);
        PCIE_DOWN_MFB_SOF_POS : in  std_logic_vector(PCIE_DOWN_REGIONS*max(1,log2(PCIE_DOWN_REGION_SIZE))-1 downto 0);
        PCIE_DOWN_MFB_EOF_POS : in  std_logic_vector(PCIE_DOWN_REGIONS*max(1,log2(PCIE_DOWN_REGION_SIZE*PCIE_DOWN_BLOCK_SIZE))-1 downto 0);
        PCIE_DOWN_MFB_SRC_RDY : in  std_logic;
        PCIE_DOWN_MFB_DST_RDY : out std_logic
    );
end entity;

architecture FULL of PCIE_PKT_READER is

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    constant REGION_WIDTH   : natural := REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant WORD_WIDTH     : natural := REGIONS*REGION_WIDTH;
    constant WORD_ITEMS     : natural := WORD_WIDTH/ITEM_WIDTH;
    constant SOF_POS_WIDTH  : natural := max(1,log2(REGION_SIZE));
    constant EOF_POS_WIDTH  : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));

    -- Internal number of Regions on the PCIe down MFB bus.
    -- Equal to PCIE_DOWN_REGIONS when USER and PCIE_DOWN MFB buses have the same width.
    -- When they do not, it contains the amount of Regions that will make the word widths equal.
    constant PCIE_DOWN_REGIONS_RESIZED : natural := WORD_WIDTH/(PCIE_DOWN_REGION_SIZE*PCIE_DOWN_BLOCK_SIZE*PCIE_DOWN_ITEM_WIDTH);

    -- Main Memory read address (specifies a word within the memory).
    constant MM_RD_ADDR_W   : natural := log2(MEMORY_SIZE);
    -- Main Memory write address (specifies a word and a byte within the memory).
    constant MM_WR_ADDR_W   : natural := log2(MEMORY_SIZE) + log2(WORD_ITEMS);

    -- Width of Tag Memory data:         MM WR addr   + packet ID + First Invalid Byte    + Last Invalid Byte
    constant TAGMEM_DATA_W  : natural := MM_WR_ADDR_W + ID_WIDTH  + DMA_REQUEST_FIRSTIB_W + DMA_REQUEST_LASTIB_W;
    -- Width of WR instr FIFO data:      vld + MM WR addr   + First Invalid Byte    + Last Invalid Byte    + ID       + tag
    constant WR_INSTR_WIDTH : natural := 1   + MM_WR_ADDR_W + DMA_REQUEST_FIRSTIB_W + DMA_REQUEST_LASTIB_W + ID_WIDTH + DMA_REQUEST_TAG_W;
    -- Max number of words a packet (MTU) can stretch over.
    constant MAX_WORDS_W    : natural := log2(div_roundup(PKT_MTU+1,WORD_ITEMS));
    -- Packet metadata width:            MM RD addr     + words       + EOFPOS in word
    constant PKT_META_W     : natural := MM_RD_ADDR_W+1 + MAX_WORDS_W + log2(WORD_ITEMS);
    -- ID Memory data width:
    --   In-order:     only tag count (metadata lives in TRANS_SORTER)
    --   Out-of-order: metadata + tag count (metadata read from IDMEM for RD instructions)
    constant IDMEM_DATA_W   : natural := tsel(RESP_IN_ORDER, DMA_REQUEST_TAG_W, PKT_META_W + DMA_REQUEST_TAG_W);
    -- TRANS_SORTER metadata width:
    --   In-order:     full metadata (output to RD instructions)
    --   Out-of-order: only MM RD addr (for freed pointer tracking)
    constant TRANS_META_W   : natural := tsel(RESP_IN_ORDER, PKT_META_W, MM_RD_ADDR_W+1);
    -- Width of RD instr FIFO data:      ID       + packet metadata
    constant RD_INSTR_W     : natural := ID_WIDTH + PKT_META_W;

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    signal pcie_uphdr_data          : std_logic_vector(REGIONS*DMA_UPHDR_WIDTH-1 downto 0);
    signal pcie_uphdr_vld           : std_logic_vector(REGIONS-1 downto 0);
    signal pcie_uphdr_src_rdy       : std_logic;
    signal pcie_uphdr_dst_rdy       : std_logic;

    signal idmem_id                 : std_logic_vector(REGIONS*ID_WIDTH-1 downto 0);
    signal idmem_addr               : std_logic_vector(REGIONS*MM_RD_ADDR_W+1-1 downto 0);
    signal idmem_words              : std_logic_vector(REGIONS*MAX_WORDS_W-1 downto 0);
    signal idmem_eof_pos            : std_logic_vector(REGIONS*log2(WORD_ITEMS)-1 downto 0);
    signal idmem_tag_cnt            : std_logic_vector(REGIONS*DMA_REQUEST_TAG_W-1 downto 0);
    signal idmem_vld                : std_logic_vector(REGIONS-1 downto 0);

    signal tagmem_tag               : std_logic_vector(REGIONS*DMA_REQUEST_TAG_W-1 downto 0);
    signal tagmem_addr              : std_logic_vector(REGIONS*MM_WR_ADDR_W-1 downto 0);
    signal tagmem_id                : std_logic_vector(REGIONS*ID_WIDTH-1 downto 0);
    signal tagmem_firstib           : std_logic_vector(REGIONS*DMA_REQUEST_FIRSTIB_W-1 downto 0);
    signal tagmem_lastib            : std_logic_vector(REGIONS*DMA_REQUEST_LASTIB_W-1 downto 0);
    signal tagmem_vld               : std_logic_vector(REGIONS-1 downto 0);

    signal free_tag                 : std_logic_vector(REGIONS*DMA_REQUEST_TAG_W-1 downto 0);
    signal free_tag_vld             : std_logic_vector(REGIONS-1 downto 0);

    signal mm_freed_rd_ptr          : std_logic_vector(MM_RD_ADDR_W+1-1 downto 0);

    signal tagmem_addr_arr          : slv_array_t(REGIONS-1 downto 0)(MM_WR_ADDR_W-1 downto 0);
    signal tagmem_id_arr            : slv_array_t(REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal tagmem_firstib_arr       : slv_array_t(REGIONS-1 downto 0)(DMA_REQUEST_FIRSTIB_W-1 downto 0);
    signal tagmem_lastib_arr        : slv_array_t(REGIONS-1 downto 0)(DMA_REQUEST_LASTIB_W-1 downto 0);
    signal tagmem_wr0_data_arr      : slv_array_t(REGIONS-1 downto 0)(TAGMEM_DATA_W-1 downto 0);

    signal tagmem_wr_addr           : slv_array_t(REGIONS + PCIE_DOWN_REGIONS - 1 downto 0)(DMA_REQUEST_TAG_W-1 downto 0);
    signal tagmem_wr_data           : slv_array_t(REGIONS + PCIE_DOWN_REGIONS - 1 downto 0)(TAGMEM_DATA_W-1 downto 0);
    signal tagmem_wr_en             : std_logic_vector(REGIONS + PCIE_DOWN_REGIONS - 1 downto 0);
    signal tagmem_rd_addr           : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(DMA_REQUEST_TAG_W-1 downto 0);
    signal tagmem_rd_data           : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(TAGMEM_DATA_W-1 downto 0);

    signal tagmem_rd_reg_addr        : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(DMA_REQUEST_TAG_W-1 downto 0);
    signal tagmem_rd_reg_data        : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(TAGMEM_DATA_W-1 downto 0);
    signal tagmem_rd_reg_len         : u_array_t(PCIE_DOWN_REGIONS-1 downto 0)(DMA_COMPLETION_LENGTH_W-1 downto 0);
    signal tagmem_rd_reg_cmpl        : std_logic_vector(PCIE_DOWN_REGIONS-1 downto 0);
    signal tagmem_rd_reg_vld         : std_logic_vector(PCIE_DOWN_REGIONS-1 downto 0);
    signal tagmem_rd_reg_intra_coll  : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(PCIE_DOWN_REGIONS-1 downto 0);
    signal tagmem_rd_reg_higher_coll : std_logic_vector(PCIE_DOWN_REGIONS-1 downto 0);

    signal tagmem_wr1_cur_addr      : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(MM_WR_ADDR_W-1 downto 0);
    signal tagmem_wr1_id            : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal tagmem_wr1_firstib       : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(DMA_REQUEST_FIRSTIB_W-1 downto 0);
    signal tagmem_wr1_lastib        : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(DMA_REQUEST_LASTIB_W-1 downto 0);
    signal tagmem_wr1_new_addr      : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(MM_WR_ADDR_W-1 downto 0);
    signal tagmem_wr1_upd_fib       : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(DMA_REQUEST_FIRSTIB_W-1 downto 0);
    signal tagmem_wr1_data_arr      : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(TAGMEM_DATA_W-1 downto 0);

    signal tagmem_base_data         : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(TAGMEM_DATA_W-1 downto 0);

    signal tagmem_inter_coll        : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(PCIE_DOWN_REGIONS-1 downto 0);
    signal tagmem_intra_coll        : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(PCIE_DOWN_REGIONS-1 downto 0);
    signal tagmem_has_higher_coll   : std_logic_vector(PCIE_DOWN_REGIONS-1 downto 0);

    signal idmem_addr_arr           : slv_array_t(REGIONS-1 downto 0)(MM_RD_ADDR_W+1-1 downto 0);
    signal idmem_words_arr          : slv_array_t(REGIONS-1 downto 0)(MAX_WORDS_W-1 downto 0);
    signal idmem_eof_pos_arr        : slv_array_t(REGIONS-1 downto 0)(log2(WORD_ITEMS)-1 downto 0);
    signal idmem_tag_cnt_arr        : slv_array_t(REGIONS-1 downto 0)(DMA_REQUEST_TAG_W-1 downto 0);
    signal idmem_wr0_data_arr       : slv_array_t(REGIONS-1 downto 0)(IDMEM_DATA_W-1 downto 0);

    signal idmem_wr_addr            : slv_array_t(2*REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal idmem_wr_data            : slv_array_t(2*REGIONS-1 downto 0)(IDMEM_DATA_W-1 downto 0);
    signal idmem_wr_en              : std_logic_vector(2*REGIONS-1 downto 0);
    signal idmem_rd_addr            : slv_array_t(REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal idmem_rd_data            : slv_array_t(REGIONS-1 downto 0)(IDMEM_DATA_W-1 downto 0);

    signal idmem_rd_reg_addr        : slv_array_t(REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal idmem_rd_reg_data        : slv_array_t(REGIONS-1 downto 0)(IDMEM_DATA_W-1 downto 0);
    signal idmem_rd_reg_cmpl        : std_logic_vector(REGIONS-1 downto 0);

    signal idmem_wr1_tagcnt         : u_array_t(REGIONS-1 downto 0)(DMA_REQUEST_TAG_W-1 downto 0);
    signal idmem_wr1_new_tag_cnt    : slv_array_t(REGIONS-1 downto 0)(DMA_REQUEST_TAG_W-1 downto 0);
    signal idmem_wr1_data_arr       : slv_array_t(REGIONS-1 downto 0)(IDMEM_DATA_W-1 downto 0);

    signal idmem_addr_collision     : std_logic;

    signal pcie_down_mvb_data_arr   : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(DMA_DOWNHDR_WIDTH-1 downto 0);
    signal pcie_resp_len            : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(DMA_COMPLETION_LENGTH_W-1 downto 0);
    signal pcie_resp_cmlp           : std_logic_vector(PCIE_DOWN_REGIONS-1 downto 0);
    signal pcie_resp_tag            : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(DMA_COMPLETION_TAG_W-1 downto 0);
    signal pcie_resp_vld            : std_logic_vector(PCIE_DOWN_REGIONS-1 downto 0);

    signal tagmem_wr1_upd_lib       : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(DMA_REQUEST_LASTIB_W-1 downto 0);
    signal tagmem_wr1_cur_addr_word : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(log2(MEMORY_SIZE)-1 downto 0);
    signal tagmem_wr1_cur_addr_byte : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(log2(WORD_ITEMS)-1 downto 0);
    signal tagmem_wr1_cur_addr_upd  : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(MM_WR_ADDR_W-1 downto 0);
    signal wr_instr_fifo_di_arr     : slv_array_t(PCIE_DOWN_REGIONS-1 downto 0)(WR_INSTR_WIDTH-1 downto 0);
    signal wr_instr_fifo_di         : std_logic_vector(PCIE_DOWN_REGIONS*WR_INSTR_WIDTH-1 downto 0);
    signal wr_instr_fifo_wr         : std_logic_vector(PCIE_DOWN_REGIONS-1 downto 0);
    signal wr_instr_fifo_full       : std_logic;
    signal wr_instr_fifo_do         : std_logic_vector(WR_INSTR_WIDTH-1 downto 0);
    signal wr_instr_fifo_rd         : std_logic_vector(1-1 downto 0);
    signal wr_instr_fifo_empty      : std_logic_vector(1-1 downto 0);

    signal wr_instr_addr_word       : unsigned(MM_RD_ADDR_W-1 downto 0);
    signal wr_instr_addr_byte       : std_logic_vector(log2(WORD_ITEMS)-1 downto 0);
    signal wr_instr_firstib         : std_logic_vector(DMA_REQUEST_FIRSTIB_W-1 downto 0);
    signal wr_instr_lastib          : std_logic_vector(DMA_REQUEST_LASTIB_W-1 downto 0);
    signal wr_instr_id              : std_logic_vector(ID_WIDTH-1 downto 0);
    signal wr_instr_tag             : std_logic_vector(DMA_REQUEST_TAG_W-1 downto 0);
    signal wr_instr_cmpl            : std_logic;
    signal wr_instr_addr_word_reg   : unsigned(MM_RD_ADDR_W-1 downto 0);
    signal wr_instr_addr_byte_reg   : std_logic_vector(log2(WORD_ITEMS)-1 downto 0);
    signal wr_instr_firstib_reg     : std_logic_vector(DMA_REQUEST_FIRSTIB_W-1 downto 0);
    signal tag_completed            : std_logic_vector(REGIONS-1 downto 0);

    signal pcie_mfb_fifo_data       : std_logic_vector(PCIE_DOWN_REGIONS*PCIE_DOWN_REGION_SIZE*PCIE_DOWN_BLOCK_SIZE*PCIE_DOWN_ITEM_WIDTH-1 downto 0);
    signal pcie_mfb_fifo_sof_pos    : std_logic_vector(PCIE_DOWN_REGIONS*max(1,log2(PCIE_DOWN_REGION_SIZE))-1 downto 0);
    signal pcie_mfb_fifo_eof_pos    : std_logic_vector(PCIE_DOWN_REGIONS*max(1,log2(PCIE_DOWN_REGION_SIZE*PCIE_DOWN_BLOCK_SIZE))-1 downto 0);
    signal pcie_mfb_fifo_sof        : std_logic_vector(PCIE_DOWN_REGIONS-1 downto 0);
    signal pcie_mfb_fifo_eof        : std_logic_vector(PCIE_DOWN_REGIONS-1 downto 0);
    signal pcie_mfb_fifo_src_rdy    : std_logic;
    signal pcie_mfb_fifo_dst_rdy    : std_logic;

    signal pcie_mfb_reconf_data     : std_logic_vector(PCIE_DOWN_REGIONS_RESIZED*PCIE_DOWN_REGION_SIZE*PCIE_DOWN_BLOCK_SIZE*PCIE_DOWN_ITEM_WIDTH-1 downto 0);
    signal pcie_mfb_reconf_sof_pos  : std_logic_vector(PCIE_DOWN_REGIONS_RESIZED*max(1,log2(PCIE_DOWN_REGION_SIZE))-1 downto 0);
    signal pcie_mfb_reconf_eof_pos  : std_logic_vector(PCIE_DOWN_REGIONS_RESIZED*max(1,log2(PCIE_DOWN_REGION_SIZE*PCIE_DOWN_BLOCK_SIZE))-1 downto 0);
    signal pcie_mfb_reconf_sof      : std_logic_vector(PCIE_DOWN_REGIONS_RESIZED-1 downto 0);
    signal pcie_mfb_reconf_eof      : std_logic_vector(PCIE_DOWN_REGIONS_RESIZED-1 downto 0);
    signal pcie_mfb_reconf_src_rdy  : std_logic;
    signal pcie_mfb_reconf_dst_rdy  : std_logic;

    signal pcie_axi_tdata           : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal pcie_axi_tkeep           : std_logic_vector(WORD_WIDTH/8-1 downto 0);
    signal pcie_axi_tlast           : std_logic;
    signal pcie_axi_tvalid          : std_logic;
    signal pcie_axi_tready          : std_logic;
    signal pkt_ends                 : std_logic;
    signal pkt_ended                : std_logic;
    signal pcie_axi_sof             : std_logic;
    signal pcie_axi_tkeep_ones      : integer;
    signal wr_instr_lastib_int      : integer;
    signal problem                  : std_logic;
    signal pcie_axi_tkeep_fixed     : std_logic_vector(WORD_WIDTH/8-1 downto 0);

    signal pcie_axi_tdata_reg       : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal pcie_axi_tkeep_reg       : std_logic_vector(WORD_WIDTH/8-1 downto 0);
    signal pcie_axi_tkeep_reg_fixed : std_logic_vector(WORD_WIDTH/8-1 downto 0);
    signal pcie_axi_tlast_reg       : std_logic;
    signal pcie_axi_tlast_reg_fixed : std_logic;
    signal pcie_axi_tvalid_reg      : std_logic;

    signal pcie_axi_sof_reg         : std_logic;

    signal bs_shift_reg             : std_logic_vector(log2(WORD_ITEMS)-1 downto 0);
    signal bs_item_vld              : std_logic_vector(WORD_ITEMS-1 downto 0);

    signal bs_shift                 : std_logic_vector(log2(WORD_ITEMS)-1 downto 0);
    signal bs_din                   : std_logic_vector(WORD_ITEMS*(ITEM_WIDTH+1)-1 downto 0);
    signal bs_ready                 : std_logic;
    signal bs_dout                  : std_logic_vector(WORD_ITEMS*(ITEM_WIDTH+1)-1 downto 0);

    signal bs_dout_arr              : slv_array_t(WORD_ITEMS-1 downto 0)(ITEM_WIDTH downto 0);
    signal bs_dout_data             : slv_array_t(WORD_ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal bs_dout_vld              : std_logic_vector(WORD_ITEMS-1 downto 0);

    signal mm_wr_addr_curr          : unsigned(MM_RD_ADDR_W-1 downto 0);
    signal mm_wr_addr_next          : unsigned(MM_RD_ADDR_W-1 downto 0);

    signal ptr                      : integer range WORD_ITEMS-1 downto 0;

    signal mm_wr_data               : slv_array_t(WORD_ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal mm_wr_addr               : slv_array_t(WORD_ITEMS-1 downto 0)(MM_RD_ADDR_W-1 downto 0);
    signal mm_wr_en                 : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal mm_rd_data               : slv_array_t(WORD_ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal mm_rd_addr               : slv_array_t(WORD_ITEMS-1 downto 0)(MM_RD_ADDR_W-1 downto 0);
    signal mm_rd_pipe_en            : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal mm_rd_curr_addr          : std_logic_vector(MM_RD_ADDR_W-1 downto 0);

    signal transs_rx_trans_id       : slv_array_t(REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal transs_rx_trans_meta     : slv_array_t(REGIONS-1 downto 0)(TRANS_META_W-1 downto 0);
    signal transs_rx_trans_src_rdy  : std_logic_vector(REGIONS-1 downto 0);
    signal transs_rx_conf_id        : slv_array_t(REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal transs_rx_conf_vld       : std_logic_vector(REGIONS-1 downto 0);
    signal transs_tx_id             : slv_array_t(REGIONS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal transs_tx_meta           : slv_array_t(REGIONS-1 downto 0)(TRANS_META_W-1 downto 0);
    signal transs_tx_src_rdy        : std_logic_vector(REGIONS-1 downto 0);
    signal transs_tx_dst_rdy_i      : std_logic;
    signal transs_tx_mm_addr        : std_logic_vector(MM_RD_ADDR_W downto 0);

    signal rd_instr_fifo_di_arr     : slv_array_t(REGIONS-1 downto 0)(RD_INSTR_W-1 downto 0);
    signal rd_instr_fifo_di         : std_logic_vector(REGIONS*RD_INSTR_W-1 downto 0);
    signal rd_instr_fifo_wr         : std_logic_vector(REGIONS-1 downto 0);
    signal rd_instr_fifo_full       : std_logic;
    signal rd_instr_fifo_do         : std_logic_vector(RD_INSTR_W-1 downto 0);
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

    assert REGIONS = 1
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
        MVB_ITEMS         => REGIONS,
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

        TX_MVB_DATA       => pcie_uphdr_data,
        TX_MVB_VLD        => pcie_uphdr_vld,
        TX_MVB_SRC_RDY    => pcie_uphdr_src_rdy,
        TX_MVB_DST_RDY    => pcie_uphdr_dst_rdy,

        IDMEM_ID          => idmem_id,
        IDMEM_ADDR        => idmem_addr,
        IDMEM_WORDS       => idmem_words,
        IDMEM_EOF_POS     => idmem_eof_pos,
        IDMEM_TAG_CNT     => idmem_tag_cnt,
        IDMEM_VLD         => idmem_vld,

        TAGMEM_TAG        => tagmem_tag,
        TAGMEM_ADDR       => tagmem_addr,
        TAGMEM_ID         => tagmem_id,
        TAGMEM_FIRSTIB    => tagmem_firstib,
        TAGMEM_LASTIB     => tagmem_lastib,
        TAGMEM_VLD        => tagmem_vld,

        TAGMEM_FREE_TAG   => free_tag,
        TAGMEM_FREE_VLD   => free_tag_vld,

        MEM_RD_PTR        => mm_freed_rd_ptr
    );

    -- NOTE: DMA headers are assigned only to Region 0, even in the case of multiple PCIE_UP_REGIONS.
    PCIE_UP_MVB_DATA(DMA_UPHDR_WIDTH-1 downto 0) <= pcie_uphdr_data(DMA_UPHDR_WIDTH-1 downto 0);
    PCIE_UP_MVB_VLD(0)                           <= pcie_uphdr_vld(0);
    PCIE_UP_MVB_SRC_RDY                          <= pcie_uphdr_src_rdy;
    pcie_uphdr_dst_rdy                           <= PCIE_UP_MVB_DST_RDY;

    free_tag     <= wr_instr_tag;
    free_tag_vld <= tag_completed;

    -- ========================================================
    --  Store records to manage responses
    -- ========================================================

    -- --------------------------------------------------------
    --  Memory for Tag records
    --
    -- The idea here is to enable memory access from two
    -- different sources at the same time:
    --   0) the Request Processor's TAGMEM interface
    --      - sets new records
    --   1) completions from PCIe down interface
    --      - uses record's data for the current completion
    --      - updates the MM WR address for the next completion
    --      - (it utilizes also the read ports)
    -- --------------------------------------------------------

    tagmem_addr_arr    <= slv_array_deser(tagmem_addr, REGIONS);
    tagmem_id_arr      <= slv_array_deser(tagmem_id, REGIONS);
    tagmem_firstib_arr <= slv_array_deser(tagmem_firstib, REGIONS);
    tagmem_lastib_arr  <= slv_array_deser(tagmem_lastib, REGIONS);
    tag_mem_wr0_g : for r in 0 to REGIONS-1 generate
        tagmem_wr0_data_arr(r) <= tagmem_addr_arr   (r) & -- MM WR address
                                  tagmem_id_arr     (r) & -- packet ID
                                  tagmem_firstib_arr(r) & -- First Inv Bytes
                                  tagmem_lastib_arr (r);  -- Last Inv Bytes
    end generate;

    -- TAGMEM source 0
    tagmem_wr_addr(REGIONS-1 downto 0) <= slv_array_deser(tagmem_tag, REGIONS);
    tagmem_wr_data(REGIONS-1 downto 0) <= tagmem_wr0_data_arr;
    tagmem_wr_en  (REGIONS-1 downto 0) <= tagmem_vld;

    -- TAGMEM records are addressed by Tags
    tag_mem_i : entity work.NP_LUTRAM
    generic map (
        DATA_WIDTH  => TAGMEM_DATA_W,
        ITEMS       => 2**DMA_REQUEST_TAG_W, -- to store all Tags
        WRITE_PORTS => REGIONS + PCIE_DOWN_REGIONS,
        READ_PORTS  => PCIE_DOWN_REGIONS,
        DEVICE      => DEVICE
    )
    port map (
        WCLK  => CLK,

        ADDRA => tagmem_wr_addr,
        DI    => tagmem_wr_data,
        WE    => tagmem_wr_en,

        ADDRB => tagmem_rd_addr,
        DOB   => tagmem_rd_data
    );

    tagmem_rd_addr <= pcie_resp_tag;

    -- -----------------------------------------------------------------
    --  TAGMEM collision detection
    --
    --  Two types of collisions can occur when multiple completion headers
    --  arrive at the same PCIE_DOWN_MVB for the same tag:
    --    1) Inter-word: tag read in current region r was also read in
    --       some region p of the previous word. The tag_mem_i output data
    --       will not contain current data in the next cycle - that is when
    --       the updated data will be written back into it. Hence we need
    --       to write the updated data also to the register (tagmem_rd_reg_data)
    --       and ignore the outdated data from the tag_mem_i (tagmem_rd_data).
    --    2) Intra-word: the same tag appears in two or more valid regions
    --       of the same word. Region h > r must use the already-updated
    --       record computed for region r.
    -- -----------------------------------------------------------------
    tagmem_inter_coll_g : for r in 0 to PCIE_DOWN_REGIONS-1 generate
        tagmem_inter_coll_p_g : for p in 0 to PCIE_DOWN_REGIONS-1 generate
            tagmem_inter_coll(r)(p) <= pcie_resp_vld(r) and tagmem_rd_reg_vld(p) when (tagmem_rd_addr(r) = tagmem_rd_reg_addr(p)) else '0';
        end generate;
    end generate;

    tagmem_intra_coll_g : for r in 0 to PCIE_DOWN_REGIONS-1 generate
        tagmem_intra_coll_c_g : for c in 0 to r-1 generate
            tagmem_intra_coll(r)(c) <= pcie_resp_vld(r) and pcie_resp_vld(c) when (tagmem_rd_addr(r) = tagmem_rd_addr(c)) else '0';
        end generate;
    end generate;

    -- In cases of intra-word collision(s), this will ensure that only the most-recently
    -- updated data will be written back to the tag_mem_i.
    tagmem_has_higher_coll_p : process (all)
        variable v_higher_coll : std_logic_vector(PCIE_DOWN_REGIONS-1 downto 0);
    begin
        for r in 0 to PCIE_DOWN_REGIONS-1 loop
            v_higher_coll(r) := '0';
            for h in r+1 to PCIE_DOWN_REGIONS-1 loop
                v_higher_coll(r) := v_higher_coll(r) or tagmem_intra_coll(h)(r);
            end loop;
        end loop;
        tagmem_has_higher_coll <= v_higher_coll;
    end process;

    -- Base data for the current computation: in the case of intra-word collision,
    -- select the data from the highest-index colliding region in the current word.
    tagmem_base_data_g : for r in 0 to PCIE_DOWN_REGIONS-1 generate
        process (all)
        begin
            tagmem_base_data(r) <= tagmem_rd_reg_data(r);
            for c in 0 to r-1 loop
                if (tagmem_rd_reg_intra_coll(r)(c) = '1') then
                    -- Use one of the already-updated calculated results in case of intra-word collision.
                    tagmem_base_data(r) <= tagmem_wr1_data_arr(c);
                end if;
            end loop;
        end process;
    end generate;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (PCIE_DOWN_MVB_DST_RDY = '1') then
                tagmem_rd_reg_addr <= tagmem_rd_addr;
                tagmem_rd_reg_data <= tagmem_rd_data;
                -- tagmem_rd_reg_data must contain actual data at colliding address in the next clock cycle.
                for r in 0 to PCIE_DOWN_REGIONS-1 loop
                    for p in 0 to PCIE_DOWN_REGIONS-1 loop
                        if (tagmem_inter_coll(r)(p) = '1') then
                            tagmem_rd_reg_data(r) <= tagmem_wr1_data_arr(p);
                        end if;
                    end loop;
                end loop;

                tagmem_rd_reg_len  <= slv_arr_to_u_arr(pcie_resp_len);
                tagmem_rd_reg_cmpl <= pcie_resp_cmlp;
                tagmem_rd_reg_vld  <= pcie_resp_vld;

                tagmem_rd_reg_intra_coll  <= tagmem_intra_coll;
                tagmem_rd_reg_higher_coll <= tagmem_has_higher_coll;
            end if;
        end if;
    end process;

    tagmem_wr1_cur_addr <= slv_array_slice(tagmem_base_data, TAGMEM_DATA_W-1, TAGMEM_DATA_W-MM_WR_ADDR_W);
    tagmem_wr1_id       <= slv_array_slice(tagmem_base_data, TAGMEM_DATA_W-MM_WR_ADDR_W-1, TAGMEM_DATA_W-MM_WR_ADDR_W-ID_WIDTH);
    tagmem_wr1_firstib  <= slv_array_slice(tagmem_base_data, TAGMEM_DATA_W-MM_WR_ADDR_W-ID_WIDTH-1, DMA_REQUEST_FIRSTIB_W);
    tagmem_wr1_lastib   <= slv_array_slice(tagmem_base_data, TAGMEM_DATA_W-MM_WR_ADDR_W-ID_WIDTH-DMA_REQUEST_FIRSTIB_W-1, 0);
    tagmem_wr1_data_g : for r in 0 to PCIE_DOWN_REGIONS-1 generate
        -- Current address + length with correction by First IB for 1st completion only.
        tagmem_wr1_new_addr(r) <= std_logic_vector(unsigned(tagmem_wr1_cur_addr(r)) + (tagmem_rd_reg_len(r) & "00") - unsigned(tagmem_wr1_firstib(r)));
        -- Set First Invalid Byte to 0 as it only plays a role in the first address update.
        tagmem_wr1_upd_fib (r) <= (others => '0');

        -- Write back updated record.
        tagmem_wr1_data_arr(r) <= tagmem_wr1_new_addr(r) & tagmem_wr1_id(r) & tagmem_wr1_upd_fib(r) & tagmem_wr1_lastib(r);
    end generate;

    -- TAGMEM source 1
    tagmem_wr_addr(REGIONS + PCIE_DOWN_REGIONS - 1 downto REGIONS) <= tagmem_rd_reg_addr;
    tagmem_wr_data(REGIONS + PCIE_DOWN_REGIONS - 1 downto REGIONS) <= tagmem_wr1_data_arr;
    tagmem_wr_en  (REGIONS + PCIE_DOWN_REGIONS - 1 downto REGIONS) <= tagmem_rd_reg_vld and not tagmem_rd_reg_higher_coll;

    -- --------------------------------------------------------
    --  Memory for ID records
    --
    -- In-order:     stores only tag count per ID (metadata lives in TRANS_SORTER)
    -- Out-of-order: stores metadata + tag count per ID (metadata read for RD instructions)
    --
    -- The idea here is to enable memory access from two different sources at the same time:
    --   0) the Request Processor's IDMEM interface
    --      - sets new records
    --   1) updates from the Tagmem
    --      - decrements the number of Tags needed to complete a whole packet
    --      - after the number of Tags reaches 0, it is sent to the RD Instr FIFO/TRANS_SORTER
    --      - (it utilizes also the read ports)
    -- --------------------------------------------------------
    idmem_addr_arr    <= slv_array_deser(idmem_addr, REGIONS);
    idmem_words_arr   <= slv_array_deser(idmem_words, REGIONS);
    idmem_eof_pos_arr <= slv_array_deser(idmem_eof_pos, REGIONS);
    idmem_tag_cnt_arr <= slv_array_deser(idmem_tag_cnt, REGIONS);
    idmem_wr0_g : if RESP_IN_ORDER generate
        idmem_wr0_data_arr <= idmem_tag_cnt_arr; -- Number of partial requests (tags)
    else generate
        idmem_wr0_data_g : for r in 0 to REGIONS-1 generate
            idmem_wr0_data_arr(r) <= idmem_addr_arr   (r) & -- MM RD address (+ new-packet flag)
                                     idmem_words_arr  (r) & -- number of words
                                     idmem_eof_pos_arr(r) & -- EOFPOS
                                     idmem_tag_cnt_arr(r);  -- Number of partial requests (tags)
        end generate;
    end generate;

    -- IDMEM source 0
    idmem_wr_addr(REGIONS-1 downto 0) <= slv_array_deser(idmem_id, REGIONS);
    idmem_wr_data(REGIONS-1 downto 0) <= idmem_wr0_data_arr;
    idmem_wr_en  (REGIONS-1 downto 0) <= idmem_vld;

    -- IDMEM records are addressed by IDs
    id_mem_i : entity work.NP_LUTRAM
    generic map (
        DATA_WIDTH  => IDMEM_DATA_W,
        ITEMS       => 2**ID_WIDTH, -- to store all IDs
        WRITE_PORTS => 2*REGIONS,
        READ_PORTS  => REGIONS,
        DEVICE      => DEVICE
    )
    port map (
        WCLK  => CLK,

        ADDRA => idmem_wr_addr,
        DI    => idmem_wr_data,
        WE    => idmem_wr_en,

        ADDRB => idmem_rd_addr,
        DOB   => idmem_rd_data
    );

    idmem_rd_addr <= (others => wr_instr_id);

    process (CLK)
    begin
        if rising_edge(CLK) then
            idmem_rd_reg_addr <= idmem_rd_addr;
            idmem_rd_reg_data <= idmem_wr1_data_arr when (idmem_addr_collision = '1') else idmem_rd_data;

            idmem_rd_reg_cmpl <= tag_completed;
        end if;
    end process;

    idmem_wr1_tagcnt <= slv_arr_to_u_arr(slv_array_slice(idmem_rd_reg_data, DMA_REQUEST_TAG_W-1, 0));

    idmem_wr1_data_g : for r in 0 to REGIONS-1 generate
        -- Decrement tag count
        idmem_wr1_new_tag_cnt(r) <= std_logic_vector(idmem_wr1_tagcnt(r) - 1);
        idmem_wr_data1_g : if RESP_IN_ORDER generate
            -- In-order: write only tag count (no metadata stored in IDMEM).
            idmem_wr1_data_arr(r) <= idmem_wr1_new_tag_cnt(r);
        else generate
            -- Out-of-order: preserve metadata, update only tag count.
            idmem_wr1_data_arr(r) <= idmem_rd_reg_data(r)(IDMEM_DATA_W-1 downto DMA_REQUEST_TAG_W) & idmem_wr1_new_tag_cnt(r);
        end generate;
    end generate;

    -- IDMEM source 1
    idmem_wr_addr(2*REGIONS-1 downto REGIONS) <= idmem_rd_reg_addr;
    idmem_wr_data(2*REGIONS-1 downto REGIONS) <= idmem_wr1_data_arr;
    idmem_wr_en  (2*REGIONS-1 downto REGIONS) <= idmem_rd_reg_cmpl;

    -- Detect colliding addresses for Tag completions in consecutive clock cycles due to registering read data (before modification and write-back).
    -- A very simple implementation for MFB Regions = 1.
    idmem_addr_collision <= idmem_rd_reg_cmpl(0) and tag_completed(0) when (unsigned(idmem_rd_reg_addr(0)) = unsigned(idmem_rd_addr(0))) else '0';

    -- ========================================================
    --  Process responses and sends them to the Main Memory
    -- ========================================================

    -- --------------------------------------------------------
    --  MVB path
    -- --------------------------------------------------------
    -- In-order: TRANS_SORTER provides extra buffer so we don't care about rd_instr_fifo_full.
    PCIE_DOWN_MVB_DST_RDY <= not wr_instr_fifo_full when (RESP_IN_ORDER) else
                             not wr_instr_fifo_full and not rd_instr_fifo_full;

    -- Data from MVB headers are used to access records in the Tag Mem
    pcie_down_mvb_data_arr <= slv_array_deser(PCIE_DOWN_MVB_DATA, PCIE_DOWN_REGIONS);
    pcie_resp_instr_g : for r in 0 to PCIE_DOWN_REGIONS-1 generate
        pcie_resp_len (r) <= pcie_down_mvb_data_arr(r)(DMA_COMPLETION_LENGTH);
        pcie_resp_cmlp(r) <= pcie_down_mvb_data_arr(r)(DMA_COMPLETION_COMPLETED_O);
        pcie_resp_tag (r) <= pcie_down_mvb_data_arr(r)(DMA_COMPLETION_TAG);
    end generate;

    pcie_resp_vld <= PCIE_DOWN_MVB_VLD and PCIE_DOWN_MVB_SRC_RDY;

    wr_instr_fifo_di_g : for r in 0 to PCIE_DOWN_REGIONS-1 generate
        -- Set Last Invalid Byte to 0 except the very last completion.
        tagmem_wr1_upd_lib(r) <= tagmem_wr1_lastib(r) when (tagmem_rd_reg_cmpl(r) = '1') else (others => '0');

        -- Update MM WR address (the part that bytes within a word/memory item).
        -- This pushed the First Invalid Bytes to the top of the word (will be invalidated and not written).
        tagmem_wr1_cur_addr_word(r) <= tagmem_wr1_cur_addr(r)(MM_WR_ADDR_W-1 downto MM_WR_ADDR_W-log2(MEMORY_SIZE));
        tagmem_wr1_cur_addr_byte(r) <= tagmem_wr1_cur_addr(r)(MM_WR_ADDR_W-log2(MEMORY_SIZE)-1 downto 0);
        tagmem_wr1_cur_addr_upd (r) <= tagmem_wr1_cur_addr_word(r) & std_logic_vector(unsigned(tagmem_wr1_cur_addr_byte(r)) - unsigned(tagmem_wr1_firstib(r)));

        wr_instr_fifo_di_arr(r) <= tagmem_rd_reg_cmpl     (r) & -- Tag completed
                                   tagmem_wr1_cur_addr_upd(r) & -- MM WR address
                                   tagmem_wr1_firstib     (r) & -- First Inv Bytes
                                   tagmem_wr1_upd_lib     (r) & -- Last Inv Bytes
                                   tagmem_wr1_id          (r) & -- packet ID
                                   tagmem_rd_reg_addr     (r);  -- request Tag
    end generate;

    -- Store write instructions (only the WR address) from the record in the Tag Mem
    wr_instr_fifo_di <= slv_array_ser(wr_instr_fifo_di_arr);
    wr_instr_fifo_wr <= tagmem_rd_reg_vld;

    wr_instr_fifo_i : entity work.FIFOX_MULTI
    generic map (
        DATA_WIDTH          => WR_INSTR_WIDTH,
        ITEMS               => 512,
        WRITE_PORTS         => PCIE_DOWN_REGIONS,
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

    -- Read with last word of packet.
    wr_instr_fifo_rd <= not wr_instr_fifo_empty and pkt_ends;

    -- Top bits address the word within the Main Memory -> used as the actual MM WR address.
    wr_instr_addr_word <= unsigned(wr_instr_fifo_do(WR_INSTR_WIDTH-1-1 downto WR_INSTR_WIDTH-1-log2(MEMORY_SIZE)));
    -- Bottom bits address the byte within the word -> used to rotate written data for proper alignment.
    wr_instr_addr_byte <= wr_instr_fifo_do(WR_INSTR_WIDTH-1-log2(MEMORY_SIZE)-1 downto WR_INSTR_WIDTH-1-MM_WR_ADDR_W);
    -- First Invalid bytes of the PCIe transaction -> used to tweak the data rotation to write only valid bytes.
    wr_instr_firstib   <= wr_instr_fifo_do(WR_INSTR_WIDTH-1-MM_WR_ADDR_W-1 downto WR_INSTR_WIDTH-1-MM_WR_ADDR_W-DMA_REQUEST_FIRSTIB_W);
    -- Last Invalid Bytes of the PCIe transaction -> used to invalidate end bytes of the data (not written to the MM).
    wr_instr_lastib    <= wr_instr_fifo_do(WR_INSTR_WIDTH-1-MM_WR_ADDR_W-DMA_REQUEST_FIRSTIB_W-1 downto WR_INSTR_WIDTH-1-MM_WR_ADDR_W-DMA_REQUEST_FIRSTIB_W-DMA_REQUEST_LASTIB_W);

    -- Packet ID to associate the instruction with the appropriate record in the ID Mem.
    wr_instr_id   <= wr_instr_fifo_do(ID_WIDTH+DMA_REQUEST_TAG_W-1 downto DMA_REQUEST_TAG_W);
    -- Completed tag number to return for reuse.
    wr_instr_tag  <= wr_instr_fifo_do(DMA_REQUEST_TAG_W-1 downto 0);
    -- Instruction (PCIe response) is the last one for this Tag -> update record in the ID Mem.
    wr_instr_cmpl <= wr_instr_fifo_do(WR_INSTR_WIDTH-1);

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (pcie_axi_sof = '1') then
                wr_instr_addr_word_reg <= wr_instr_addr_word;
                wr_instr_addr_byte_reg <= wr_instr_addr_byte;
                wr_instr_firstib_reg   <= wr_instr_firstib;
            end if;
        end if;
    end process;

    tag_completed <= (others => wr_instr_cmpl and wr_instr_fifo_rd(0));

    -- --------------------------------------------------------
    --  Store response packets
    -- --------------------------------------------------------
    mfb_fifox_i : entity work.MFB_FIFOX
    generic map (
        REGIONS             => PCIE_DOWN_REGIONS,
        REGION_SIZE         => PCIE_DOWN_REGION_SIZE,
        BLOCK_SIZE          => PCIE_DOWN_BLOCK_SIZE,
        ITEM_WIDTH          => PCIE_DOWN_ITEM_WIDTH,
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
    --  Eventually resize PCIe MFB bus to be the same width as USER MFB.
    -- --------------------------------------------------------
    pcie_mfb_reconfigurator_i : entity work.MFB_RECONFIGURATOR
    generic map (
        RX_REGIONS            => PCIE_DOWN_REGIONS,
        RX_REGION_SIZE        => PCIE_DOWN_REGION_SIZE,
        RX_BLOCK_SIZE         => PCIE_DOWN_BLOCK_SIZE,
        RX_ITEM_WIDTH         => PCIE_DOWN_ITEM_WIDTH,
        TX_REGIONS            => PCIE_DOWN_REGIONS_RESIZED,
        TX_REGION_SIZE        => PCIE_DOWN_REGION_SIZE,
        TX_BLOCK_SIZE         => PCIE_DOWN_BLOCK_SIZE,
        TX_ITEM_WIDTH         => PCIE_DOWN_ITEM_WIDTH,
        META_WIDTH            => 0,
        META_MODE             => 0,
        FIFO_SIZE             => 32,
        FRAMES_OVER_TX_BLOCK  => 0,
        FRAMES_OVER_TX_REGION => 0,
        DEVICE                => DEVICE
    )
    port map (
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => pcie_mfb_fifo_data,
        RX_META    => (others => '0'),
        RX_SOF     => pcie_mfb_fifo_sof,
        RX_EOF     => pcie_mfb_fifo_eof,
        RX_SOF_POS => pcie_mfb_fifo_sof_pos,
        RX_EOF_POS => pcie_mfb_fifo_eof_pos,
        RX_SRC_RDY => pcie_mfb_fifo_src_rdy,
        RX_DST_RDY => pcie_mfb_fifo_dst_rdy,

        TX_DATA    => pcie_mfb_reconf_data,
        TX_META    => open,
        TX_SOF     => pcie_mfb_reconf_sof,
        TX_EOF     => pcie_mfb_reconf_eof,
        TX_SOF_POS => pcie_mfb_reconf_sof_pos,
        TX_EOF_POS => pcie_mfb_reconf_eof_pos,
        TX_SRC_RDY => pcie_mfb_reconf_src_rdy,
        TX_DST_RDY => pcie_mfb_reconf_dst_rdy
    );

    -- --------------------------------------------------------
    --  Use MFB2AXI to get only one packet per word.
    -- --------------------------------------------------------
    mfb2axi_i : entity work.MFB2AXI
    generic map (
        USE_IN_PIPE    => True,
        USE_OUT_PIPE   => True,
        REGIONS        => PCIE_DOWN_REGIONS_RESIZED,
        REGION_SIZE    => PCIE_DOWN_REGION_SIZE,
        BLOCK_SIZE     => PCIE_DOWN_BLOCK_SIZE,
        ITEM_WIDTH     => PCIE_DOWN_ITEM_WIDTH,
        AXI_DATA_WIDTH => REGION_WIDTH,
        PIPE_TYPE      => "SHREG",
        DEVICE         => DEVICE
    )
    port map (
        CLK            => CLK,
        RST            => RESET,

        RX_MFB_DATA    => pcie_mfb_reconf_data,
        RX_MFB_SOF_POS => pcie_mfb_reconf_sof_pos,
        RX_MFB_EOF_POS => pcie_mfb_reconf_eof_pos,
        RX_MFB_SOF     => pcie_mfb_reconf_sof,
        RX_MFB_EOF     => pcie_mfb_reconf_eof,
        RX_MFB_SRC_RDY => pcie_mfb_reconf_src_rdy,
        RX_MFB_DST_RDY => pcie_mfb_reconf_dst_rdy,

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
            if ((RESET = '1') or (pkt_ends = '1')) then
                pkt_ended <= '1';
            end if;
        end if;
    end process;
    pkt_ends <= pcie_axi_tlast and pcie_axi_tvalid and pcie_axi_tready;

    pcie_axi_sof <= pkt_ended and pcie_axi_tvalid and pcie_axi_tready;

    -- --------------------------------------------------------
    --  Remove invalid bytes
    -- --------------------------------------------------------
    pcie_axi_tkeep_ones <= count_ones(pcie_axi_tkeep);
    wr_instr_lastib_int <= to_integer(unsigned(wr_instr_lastib));

    -- Removing Last Invalid Bytes underflows the current word.
    -- -> Invalidate this word and set TLAST and adjust TKEEP in the next word;
    --    see pcie_axi_tlast_reg_fixed, pcie_axi_tkeep_reg_fixed.
    problem <= pcie_axi_tlast and pcie_axi_tvalid when (wr_instr_lastib_int >= pcie_axi_tkeep_ones) else '0';

    process (all)
    begin
        pcie_axi_tkeep_fixed <= pcie_axi_tkeep;
        -- Invalidate bytes at the Start Of Frame.
        if (pcie_axi_sof = '1') then
            pcie_axi_tkeep_fixed(to_integer(unsigned(wr_instr_firstib))-1 downto 0) <= (others => '0');
        end if;
        -- Invalidate bytes at the End Of Frame.
        if ((pkt_ends = '1') and (problem = '0')) then
            pcie_axi_tkeep_fixed(WORD_ITEMS-1 downto pcie_axi_tkeep_ones-wr_instr_lastib_int) <= (others => '0');
        end if;
    end process;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (pcie_axi_tready = '1') then
                pcie_axi_tdata_reg  <= pcie_axi_tdata;
                pcie_axi_tkeep_reg  <= pcie_axi_tkeep_fixed;
                pcie_axi_tlast_reg  <= pcie_axi_tlast;
            end if;
            pcie_axi_tvalid_reg <= pcie_axi_tvalid and not problem and not wr_instr_fifo_empty(0);
            pcie_axi_sof_reg    <= pcie_axi_sof;
            if (RESET = '1') then
                pcie_axi_tvalid_reg <= '0';
            end if;
        end if;
    end process;

    process (all)
    begin
        pcie_axi_tkeep_reg_fixed <= pcie_axi_tkeep_reg;
        -- Invalidate bytes at the End Of Frame when Last Invalid Bytes underflow into this word.
        if (problem = '1') then
            pcie_axi_tkeep_reg_fixed(WORD_ITEMS-1 downto WORD_ITEMS-(wr_instr_lastib_int-pcie_axi_tkeep_ones)) <= (others => '0');
        end if;
    end process;
    pcie_axi_tlast_reg_fixed <= '1' when (problem = '1') else pcie_axi_tlast_reg;

    -- --------------------------------------------------------
    --  Rotate write data to write them to the correct places within each word of the MM
    -- --------------------------------------------------------
    process (CLK)
    begin
        if rising_edge(CLK) then
            bs_shift_reg <= bs_shift;
        end if;
    end process;

    -- Validates Items of the current packet until EOF, used as WR Enable for the MM.
    bs_item_vld <= pcie_axi_tkeep_reg_fixed and pcie_axi_tvalid_reg;

    bs_din   <= slv_array_ser(concat_arr(slv_array_deser(pcie_axi_tdata_reg, WORD_ITEMS), bs_item_vld));
    bs_shift <= wr_instr_addr_byte_reg when (pcie_axi_sof_reg = '1') else bs_shift_reg;

    barrel_shifter_i : entity work.BARREL_SHIFTER_GEN_PIPED
    generic map (
        BLOCKS            => WORD_ITEMS,
        BLOCK_WIDTH       => ITEM_WIDTH+1,
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
        bs_dout_data(i) <= bs_dout_arr(i)(ITEM_WIDTH-1 downto 0);
        bs_dout_vld (i) <= bs_dout_arr(i)(ITEM_WIDTH);
    end generate;

    -- ========================================================
    --  The Main Memory (MM)
    --    - stores the partial responses from PCIe
    --      => completes packets for the user
    -- ========================================================

    -- --------------------------------------------------------
    --  Main Memory Write addresses
    --    - data words are rotated to follow up on the previously
    --      written data. That leads to writing to 2 addresses
    --      at once (mm_wr_addr_curr and mm_wr_addr_next).
    -- --------------------------------------------------------
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (pcie_axi_sof_reg = '1') then
                mm_wr_addr_curr <= wr_instr_addr_word_reg;
                -- The Barrel Shifter rotates UP -> that would move the valid bytes to the next word, which uses mm_wr_addr_next
                if (or wr_instr_firstib_reg = '1') then
                    mm_wr_addr_next <= wr_instr_addr_word_reg;
                else
                    mm_wr_addr_next <= wr_instr_addr_word_reg + 1;
                end if;
            -- Increment addresses with consecutive valid writes.
            elsif (or bs_dout_vld = '1') then
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
            DATA_WIDTH     => ITEM_WIDTH,
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

    rd_instr_input_g : if RESP_IN_ORDER generate
        -- In-order: RD instructions come from TRANS_SORTER output (sorted by original request order)
        rd_instr_fifo_wr <= transs_tx_src_rdy;
        rd_instr_fifo_g : for r in 0 to REGIONS-1 generate
            rd_instr_fifo_di_arr(r) <= transs_tx_id(r) & transs_tx_meta(r);
        end generate;
    else generate
        -- Out-of-order: RD instructions come directly from ID Memory when all tags complete
        rd_instr_fifo_g : for r in 0 to REGIONS-1 generate
            rd_instr_fifo_wr    (r) <= idmem_rd_reg_cmpl(r) when (idmem_wr1_tagcnt(r) = 1) else '0';
            rd_instr_fifo_di_arr(r) <= idmem_rd_reg_addr(r) & idmem_rd_reg_data(r)(IDMEM_DATA_W-1 downto DMA_REQUEST_TAG_W);
        end generate;
    end generate;
    rd_instr_fifo_di <= slv_array_ser(rd_instr_fifo_di_arr);

    -- Store read instructions
    rd_instr_fifo_i : entity work.FIFOX_MULTI
    generic map (
        DATA_WIDTH          => RD_INSTR_W,
        ITEMS               => 64,
        WRITE_PORTS         => REGIONS,
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
    --  In-order output and read address freeing
    -- ========================================================

    -- Pass metadata to TRANS_SORTER when a new request arrives
    transs_rx_trans_id      <= slv_array_deser(idmem_id, REGIONS);
    transs_rx_trans_meta_g : if RESP_IN_ORDER generate
        -- In-order: full metadata (output to RD instructions)
        transs_rx_trans_meta_full_g : for r in 0 to REGIONS-1 generate
            transs_rx_trans_meta(r) <= idmem_addr_arr   (r) & -- MM RD address
                                       idmem_words_arr  (r) & -- number of words
                                       idmem_eof_pos_arr(r);  -- EOFPOS
        end generate;
    else generate
        -- Out-of-order: only MM RD address (for freed pointer tracking)
        transs_rx_trans_meta <= idmem_addr_arr;
    end generate;
    transs_rx_trans_src_rdy <= idmem_vld;

    -- Confirm to TRANS_SORTER when all tags for an ID have completed
    transs_rx_conf_id  <= idmem_rd_reg_addr;
    transs_rx_conf_g : for r in 0 to REGIONS-1 generate
        transs_rx_conf_vld(r) <= idmem_rd_reg_cmpl(r) when (idmem_wr1_tagcnt(r) = 1) else '0';
    end generate;

    trans_sorter_i : entity work.TRANS_SORTER
    generic map (
        RX_TRANSS           => REGIONS,
        TX_TRANSS           => REGIONS,
        ID_CONFS            => REGIONS,
        ID_WIDTH            => ID_WIDTH,
        TRANS_FIFO_ITEMS    => 2**ID_WIDTH, -- enough for RX_TRANS_DST_RDY and/or TRANS_FIFO_AFULL to never fire
        METADATA_WIDTH      => TRANS_META_W,
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

        TX_TRANS_ID      => transs_tx_id,
        TX_TRANS_META    => transs_tx_meta,
        TX_TRANS_SRC_RDY => transs_tx_src_rdy,
        TX_TRANS_DST_RDY => transs_tx_dst_rdy_i
    );

    -- Out-of-order: always drain TRANS_SORTER output (used only for mm_freed_rd_ptr tracking)
    transs_tx_dst_rdy_i <= not rd_instr_fifo_full when (RESP_IN_ORDER) else '1';

    -- Extract MM read address from TRANS_SORTER metadata
    transs_tx_mm_addr <= transs_tx_meta(0) when (not RESP_IN_ORDER) else
                         transs_tx_meta(0)(TRANS_META_W-1 downto MAX_WORDS_W+log2(WORD_ITEMS));

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (transs_tx_src_rdy(0) = '1') then
                mm_freed_rd_ptr <= transs_tx_mm_addr;
            end if;
            if (RESET = '1') then
                mm_freed_rd_ptr <= (others => '0');
            end if;
        end if;
    end process;

end architecture;
