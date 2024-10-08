-- crossbarx_stream.vhd: Crossbarx stream
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- =========================================================================
--  Description
-- =========================================================================

-- This unit can:
--
-- - discard packets,
-- - insert gaps between packets and
-- - extend and/or shrink them from the front and/or from the back.
--
-- The CrossbarX component transfers the transactions from the Input buffer
-- to the Output buffer according to the instructions provided by the Packet
-- Planner component.
-- The instructions consist of a transaction's length, its address in the
-- Input buffer, and in the Output buffer.
entity CROSSBARX_STREAM is
generic(
    -- Clock settings for 1) CrossbarX and 2) Output buffer
    -- 1) CrossbarX
    -- Transfer data on double frequency Clock.
    CX_USE_CLK2           : boolean := true;
    -- Transfer data on arbitrary frequency Clock.
    -- (Overrides CX_USE_CLK2 when set to True.)
    -- See entity of CrossbarX for more detail.
    CX_USE_CLK_ARB        : boolean := false;
    -- 2) Output buffer
    -- Set True when RX_CLK has the same period as TX_CLK.
    OBUF_META_EQ_OUTPUT   : boolean := false;
    -- Set True when not using CLK2 or CLK_ARB and
    -- RX_CLK has the same period as TX_CLK.
    OBUF_INPUT_EQ_OUTPUT  : boolean := false;

    -- Number of Regions within a data word, must be power of 2.
    MFB_REGIONS           : natural := 4;
    -- Region size (in Blocks).
    MFB_REGION_SIZE       : natural := 8;
    -- Block size (in Items).
    MFB_BLOCK_SIZE        : natural := 8;
    -- Item width (in bits), must be 8.
    MFB_ITEM_WIDTH        : natural := 8;
    -- Width of MFB metadata (in bits).
    MFB_META_WIDTH        : natural := 1;

    -- Maximum packet size in MFB ITEMS.
    PKT_MTU               : natural := 1024;

    -- Number of maximum sized packets in Input and Output buffer
    -- MUST be a power of 2
    -- (4 -> ~150 Gb/s, 8 -> ~400 Gb/s)
    NUM_OF_PKTS           : natural := 4;

    -- Maximum number of Transaction waiting for data transfer.
    -- Setting this value too low will lead to lower throughput,
    -- which should trigger a simulation assert warning in component CrossbarX.
    TRANS_FIFO_SIZE       : natural := 64;

    -- CrossbarX Stream functions setup ------------------------------------
    -- Insert gaps of defined size between packets.
    -- When set to False, the smallest possible gap is used.
    F_GAP_ADJUST_EN       : boolean := false;
    -- Required average gap after every packet in MFB ITEMS.
    -- Differences in gaps are calculated according to the Deficit Idle Count algorithm.
    -- If AVG size is equal to MIN size, all gap sizes will be greater or equal to MIN size.
    -- MUST be greater or equal to F_GAP_ADJUST_SIZE_MIN!
    F_GAP_ADJUST_SIZE_AVG : natural := 24;
    -- MUST be greater or equal to MFB_BLOCK_SIZE!
    F_GAP_ADJUST_SIZE_MIN : natural := 24;

    -- Enable to extend (or shrink) packets at the front.
    F_EXTEND_START_EN     : boolean := false;
    -- In MFB ITEMS, negative number for packet shrinking.
    F_EXTEND_START_SIZE   : integer := -4;

    -- Enable to extend (or shrink) packets at the back.
    F_EXTEND_END_EN       : boolean := false;
    -- In MFB ITEMS, negative number for packet shrinking.
    F_EXTEND_END_SIZE     : integer := -5;

    -- FPGA device name: ULTRASCALE, STRATIX10, ..
    DEVICE                : string := "STRATIX10"
);
port(
    -- =====================================================================
    --  Clock and Reset
    -- =====================================================================

    RX_CLK         : in  std_logic;
    -- Double frequency and same source as RX_CLK
    -- Only used when CX_USE_CLK2==True and CX_USE_CLK_ARB==False
    RX_CLK2        : in  std_logic;
    RX_RESET       : in  std_logic;
    TX_CLK         : in  std_logic;
    TX_RESET       : in  std_logic;
    -- Arbitrary Clock and Reset for CrossbarX, only used when CX_USE_CLK_ARB==True
    CX_CLK_ARB     : in  std_logic;
    CX_RESET_ARB   : in  std_logic;

    -- =====================================================================
    --  RX MFB STREAM
    -- =====================================================================

    RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- valid with EOF
    RX_MFB_META    : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
    -- valid with EOF
    RX_MFB_DISCARD : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_SRC_RDY : in  std_logic;
    RX_MFB_DST_RDY : out std_logic;

    -- =====================================================================
    --  TX MFB STREAM
    -- =====================================================================

    TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- valid with EOF
    TX_MFB_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_SRC_RDY : out std_logic;
    TX_MFB_DST_RDY : in  std_logic
);
end entity;

architecture FULL of CROSSBARX_STREAM is

    function ALLOW_BLOCK_SIZE_1 return boolean is
    begin
        --pragma synthesis_off
        return true;
        --pragma synthesis_on
        return false;
    end function;

    -- Change DEVICE to "NONE" if this is a simulation
    -- altera_syncram does not work correctly in simulation in some configurations
    -- Using "NONE" device switches the memory to behavioral architecture
    function SDP_BRAM_DEVICE return string is
        variable dev0 : string(DEVICE'range) := DEVICE;
        variable dev1 : string(1 to 3) := "SIM";
    begin
        --pragma synthesis_off
        if (DEVICE = "STRATIX10" or DEVICE = "ARRIA10") then
            return dev1;
        end if;
        --pragma synthesis_on
        return dev0;
    end function;

    constant MFB_REGION_WIDTH : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant MFB_DATA_WIDTH   : natural := MFB_REGIONS*MFB_REGION_WIDTH;

    constant BUF_WORDSL       : natural := log2(PKT_MTU*MFB_ITEM_WIDTH/MFB_DATA_WIDTH*NUM_OF_PKTS*2-1);
    constant RX_BUF_WORDS     : natural := 2**BUF_WORDSL;
    constant TX_BUF_WORDS     : natural := 2**BUF_WORDSL;

    constant ROW_WIDTH        : natural := MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant BUF_ROWS         : natural := MFB_REGIONS*MFB_REGION_SIZE;

    constant GAP_SIZE_AVG     : natural := tsel(F_GAP_ADJUST_EN, F_GAP_ADJUST_SIZE_AVG, MFB_BLOCK_SIZE);
    constant GAP_SIZE_MIN     : natural := tsel(F_GAP_ADJUST_EN, F_GAP_ADJUST_SIZE_MIN, MFB_BLOCK_SIZE);

    -- =====================================================================
    -- Modifications of Clock and Reset signals
    -- =====================================================================
    signal cx_data_inf_clk    : std_logic;
    signal cx_data_inf_reset  : std_logic;

    -- =====================================================================
    --  Packet length calculation
    -- =====================================================================
    constant FR_LEN_META_WIDTH : natural := MFB_META_WIDTH + 1;

    signal rx_mfb_meta_arr     : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH-1 downto 0);
    signal rx_mfb_discard_vld  : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal fr_len_rx_meta_arr  : slv_array_t     (MFB_REGIONS-1 downto 0)(FR_LEN_META_WIDTH-1 downto 0);
    signal fr_len_rx_meta      : std_logic_vector(MFB_REGIONS*FR_LEN_META_WIDTH-1 downto 0);

    signal fr_len_tx_data      : std_logic_vector(MFB_DATA_WIDTH-1 downto 0);
    signal fr_len_tx_meta      : std_logic_vector(MFB_REGIONS*FR_LEN_META_WIDTH-1 downto 0);
    signal fr_len_tx_length    : std_logic_vector(MFB_REGIONS*log2(PKT_MTU+1)-1 downto 0);
    signal fr_len_tx_sof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fr_len_tx_eof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fr_len_tx_sof_pos   : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal fr_len_tx_src_rdy   : std_logic;
    signal fr_len_tx_dst_rdy   : std_logic;

    -- =====================================================================
    --  RX Buffer data writing logic
    -- =====================================================================
    constant RX_BUF_PTR_WIDTH  : natural := log2(RX_BUF_WORDS) + log2(BUF_ROWS*MFB_BLOCK_SIZE);
    --                                      rx_buf_rd_ptr    + discard
    constant FIFOXM_DATA_WIDTH : natural := RX_BUF_PTR_WIDTH + 1;

    signal rx_buf_ptr_with_discard_arr : slv_array_t     (MFB_REGIONS-1 downto 0)(FIFOXM_DATA_WIDTH-1 downto 0);
    signal rx_buf_fifoxm_di            : std_logic_vector(MFB_REGIONS*            FIFOXM_DATA_WIDTH-1 downto 0);
    signal rx_buf_fifoxm_wr            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_buf_fifoxm_full          : std_logic;
    signal rx_buf_fifoxm_do            : std_logic_vector(MFB_REGIONS*            FIFOXM_DATA_WIDTH-1 downto 0);
    signal rx_buf_fifoxm_do_arr        : slv_array_t     (MFB_REGIONS-1 downto 0)(FIFOXM_DATA_WIDTH-1 downto 0);
    signal rx_buf_fifoxm_rd            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_buf_fifoxm_empty         : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal src_rdy0_fifoxm             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal dst_rdy0_fifoxm             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal dst_rdy0_remapped           : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal rx_buf_pkt_sent             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_buf_discard              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_buf_rd_ptr               : u_array_t       (MFB_REGIONS-1 downto 0)(RX_BUF_PTR_WIDTH-1 downto 0);

    signal rx_buf_rd_ptr_reg           : unsigned        (RX_BUF_PTR_WIDTH-1 downto 0);
    signal rx_buf_wr_ptr_reg           : unsigned        (log2(RX_BUF_WORDS)-1 downto 0);
    signal rx_buf_wr_ptr_inc_reg       : unsigned        (log2(RX_BUF_WORDS)-1 downto 0);
    signal rx_buf_full                 : std_logic;

    -- =====================================================================
    --  Transaction Generator
    -- =====================================================================
    --                                        MFB meta       + discard
    constant TRGEN_META_WIDTH    : natural := MFB_META_WIDTH + 1;

    signal trgen_mfb_sof_addr    : std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    signal trgen_mfb_sof_pos_arr : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE)-1 downto 0);
    signal trgen_mfb_sof_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal trgen_mfb_meta_arr    : slv_array_t     (MFB_REGIONS-1 downto 0)(TRGEN_META_WIDTH-1 downto 0);
    signal trgen_mfb_length_arr  : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal trgen_mfb_eof_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal trgen_mfb_src_rdy     : std_logic;
    signal trgen_mfb_dst_rdy     : std_logic;

    signal trgen_trans_a_col     : std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    signal trgen_trans_a_item    : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal trgen_trans_meta_arr  : slv_array_t     (MFB_REGIONS-1 downto 0)(TRGEN_META_WIDTH-1 downto 0);
    signal trgen_trans_mfb_meta  : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH-1 downto 0);
    signal trgen_trans_discard   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal trgen_trans_addr      : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(RX_BUF_WORDS)+log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal trgen_trans_addr_mod  : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(RX_BUF_WORDS)+log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal trgen_trans_len_arr   : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal trgen_trans_vld       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal trgen_trans_src_rdy   : std_logic;
    signal trgen_trans_dst_rdy   : std_logic;

    -- =====================================================================
    -- Packet planner (Gap Counter)
    -- =====================================================================
    --                                       Input buffer address                               + metadata
    constant PACP_META_WIDTH    : natural := log2(RX_BUF_WORDS) + log2(BUF_ROWS*MFB_BLOCK_SIZE) + MFB_META_WIDTH;
    constant PCAP_SPACE_SIZE    : natural := TX_BUF_WORDS*MFB_DATA_WIDTH/MFB_ITEM_WIDTH;

    signal pacp_rx_pkt_meta     : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(PACP_META_WIDTH-1 downto 0);
    signal pacp_rx_pkt_len_mod1 : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal pacp_rx_pkt_len_mod2 : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal pacp_rx_pkt_len_mod3 : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal pacp_rx_pkt_vld      : slv_array_t     (1-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal pacp_rx_pkt_src_rdy  : std_logic_vector(1-1 downto 0);
    signal pacp_rx_pkt_afull    : std_logic_vector(1-1 downto 0);

    signal pacp_space_rd_ptr    : std_logic_vector(log2(TX_BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE)-1 downto 0);
    signal pacp_tx_pkt_meta     : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(PACP_META_WIDTH-1 downto 0);
    signal pacp_tx_mfb_meta     : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH-1 downto 0);
    signal pacp_tx_pkt_a_col    : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    signal pacp_tx_pkt_a_item   : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal pacp_tx_pkt_len      : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal pacp_tx_pkt_len_mod1 : u_array_t       (MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal pacp_tx_pkt_len_mod2 : u_array_t       (MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal pacp_tx_pkt_len_mod3 : u_array_t       (MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal pacp_tx_pkt_addr     : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)+log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal pacp_tx_pkt_addr_mod : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)+log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal pacp_tx_pkt_vld      : slv_array_t     (1-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal pacp_tx_pkt_dst_rdy  : slv_array_t     (1-1 downto 0)(MFB_REGIONS-1 downto 0);

    signal gapc_trans_a_col     : std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    signal gapc_trans_a_item    : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal gapc_trans_b_col     : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    signal gapc_trans_b_item    : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal gapc_trans_len       : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal gapc_trans_vld       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal gapc_trans_src_rdy   : std_logic;

    -- =====================================================================
    --  RX Buffer
    -- =====================================================================
    constant RX_BUF_COMMON_CLK : boolean := not (CX_USE_CLK2 or CX_USE_CLK_ARB);

    signal rx_buf_wr_addr      : slv_array_t     (BUF_ROWS-1 downto 0)(log2(RX_BUF_WORDS)-1 downto 0);
    signal rx_buf_wr_data      : slv_array_t     (BUF_ROWS-1 downto 0)(ROW_WIDTH-1 downto 0);
    signal rx_buf_wr_en        : std_logic_vector(BUF_ROWS-1 downto 0);

    signal rx_buf_rd_addr_ser  : std_logic_vector(BUF_ROWS*log2(RX_BUF_WORDS)-1 downto 0);
    signal rx_buf_rd_addr      : slv_array_t     (BUF_ROWS-1 downto 0)(log2(RX_BUF_WORDS)-1 downto 0);
    signal rx_buf_rd_data      : slv_array_t     (BUF_ROWS-1 downto 0)(ROW_WIDTH-1 downto 0);

    -- =====================================================================
    --  CrossbarX
    -- =====================================================================
    --                                            metadata       + packet length   + address in Output buffer
    constant CROX_META_WIDTH        : integer :=  MFB_META_WIDTH + log2(PKT_MTU+1) + log2(TX_BUF_WORDS*BUF_ROWS*MFB_BLOCK_SIZE);

    signal crox_instr_a_col         : slv_array_t     (1-1 downto 0)                        (log2(RX_BUF_WORDS)-1 downto 0);
    signal crox_instr_b_col         : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);

    signal crox_instr_a_item        : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal crox_instr_b_item        : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal crox_instr_len           : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);

    signal crox_instr_meta          : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(CROX_META_WIDTH-1 downto 0);
    signal crox_instr_vld           : slv_array_t     (1-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal crox_instr_src_rdy       : std_logic_vector(1-1 downto 0);
    signal crox_instr_dst_rdy       : std_logic_vector(1-1 downto 0);

    signal crox_src_buf_rd_addr_ser : std_logic_vector(BUF_ROWS*log2(RX_BUF_WORDS)-1 downto 0);
    signal crox_src_buf_rd_addr     : slv_array_t     (BUF_ROWS-1 downto 0)(log2(RX_BUF_WORDS)-1 downto 0);
    signal crox_src_buf_rd_data     : slv_array_t     (BUF_ROWS-1 downto 0)(ROW_WIDTH-1 downto 0);

    signal crox_dst_buf_wr_addr     : slv_array_t     (BUF_ROWS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    signal crox_dst_buf_wr_data     : slv_array_t     (BUF_ROWS-1 downto 0)(ROW_WIDTH-1 downto 0);
    signal crox_dst_buf_wr_ie       : slv_array_t     (BUF_ROWS-1 downto 0)(MFB_BLOCK_SIZE-1 downto 0); -- item enable
    signal crox_dst_buf_wr_en       : std_logic_vector(BUF_ROWS-1 downto 0);

    signal crox_comp_meta           : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(CROX_META_WIDTH-1 downto 0);
    signal crox_comp_mfb_meta       : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH-1 downto 0);
    signal crox_comp_len            : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal crox_comp_addr           : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)+log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    -- Width +1 because crox metadata are concatenated with src_rdy1_asfifox (serves as valid)
    signal crox_meta_with_vld       : slv_array_t     (MFB_REGIONS-1 downto 0)(CROX_META_WIDTH+1-1 downto 0);
    signal crox_comp_src_rdy        : slv_array_t     (1-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal crox_comp_dst_rdy        : slv_array_t     (1-1 downto 0)(MFB_REGIONS-1 downto 0);

    -- =====================================================================
    --  ASFIFOX
    -- =====================================================================
    --                                                    metadata        + src_rdy1_asfifox (= valid)
    constant ASFIFOX_DATA_WIDTH : natural := MFB_REGIONS*(CROX_META_WIDTH + 1);

    signal asfifox_wr_data     : std_logic_vector(ASFIFOX_DATA_WIDTH-1 downto 0);
    signal asfifox_wr_en       : std_logic;
    signal asfifox_wr_full     : std_logic;

    signal asfifox_rd_data     : std_logic_vector(ASFIFOX_DATA_WIDTH-1 downto 0);
    signal asfifox_rd_en       : std_logic;
    signal asfifox_rd_data_arr : slv_array_t     (MFB_REGIONS-1 downto 0)(ASFIFOX_DATA_WIDTH/MFB_REGIONS-1 downto 0);
    signal asfifox_rd_empty    : std_logic;

    signal asfifox_wr_possible : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal src_rdy1_asfifox    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal dst_rdy1_asfifox    : std_logic;

    -- =====================================================================
    --  TX Buffer
    -- =====================================================================
    signal tx_buf_wr_data          : slv_array_t     (BUF_ROWS-1 downto 0)(ROW_WIDTH-1 downto 0);
    signal tx_buf_wr_addr          : slv_array_t     (BUF_ROWS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    signal tx_buf_wr_ie            : slv_array_t     (BUF_ROWS-1 downto 0)(MFB_BLOCK_SIZE-1 downto 0);
    signal tx_buf_wr_en            : std_logic_vector(BUF_ROWS-1 downto 0);

    signal tx_buf_rx_instr_meta    : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH-1 downto 0);
    signal tx_buf_rx_instr_len     : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal tx_buf_rx_instr_dst_row : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(MFB_DATA_WIDTH/MFB_ITEM_WIDTH)-1 downto 0);
    signal tx_buf_rx_instr_dst_col : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    signal tx_buf_rx_instr_addr    : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(MFB_DATA_WIDTH/MFB_ITEM_WIDTH)+log2(TX_BUF_WORDS)-1 downto 0);
    signal tx_buf_rx_instr_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_buf_rx_instr_src_rdy : std_logic;
    signal tx_buf_rx_instr_dst_rdy : std_logic;

    signal tx_buf_rd_ptr_addr      : std_logic_vector(log2(TX_BUF_WORDS*BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);

    signal tx_buf_tx_meta          : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal tx_buf_tx_mvb_vld       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_buf_tx_mvb_src_rdy   : std_logic;
    signal tx_buf_tx_mvb_dst_rdy   : std_logic;

    signal tx_buf_tx_mfb_data      : std_logic_vector(MFB_DATA_WIDTH-1 downto 0);
    signal tx_buf_tx_mfb_sof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_buf_tx_mfb_eof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_buf_tx_mfb_sof_pos   : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal tx_buf_tx_mfb_eof_pos   : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal tx_buf_tx_mfb_src_rdy   : std_logic;
    signal tx_buf_tx_mfb_dst_rdy   : std_logic;

begin

    assert ((GAP_SIZE_AVG >= GAP_SIZE_MIN) and (GAP_SIZE_MIN >= MFB_BLOCK_SIZE))
        report "GAP_SIZE_AVG >= GAP_SIZE_MIN >= MFB_BLOCK_SIZE must apply!"
        severity failure;

    -- Some workaround should be created in the future
    assert ((MFB_BLOCK_SIZE > 1) or ALLOW_BLOCK_SIZE_1)
        report "Due to a bug in Vivado 2019, MFB_BLOCK_SIZE must be greater than 1."
        severity failure;

    assert not (OBUF_META_EQ_OUTPUT and OBUF_INPUT_EQ_OUTPUT and (CX_USE_CLK2 or CX_USE_CLK_ARB))
        report "Watch out for Clock settings! OBUF_META_EQ_OUTPUT and OBUF_INPUT_EQ_OUTPUT can't be both True when RX_CLK2 or CX_CLK_ARB is used!"
        severity failure;

    -- first_debug_p : process (RX_CLK)
    -- begin
    --     if (rising_edge(RX_CLK)) then
    --         if ((RX_MFB_SRC_RDY = '1') and (RX_MFB_DST_RDY = '1')) then
    --             report "CX stream: MFB DATA: " &
    --                    to_hstring(RX_MFB_DATA)
    --             severity note;
    --         end if;
    --     end if;
    -- end process;

    -- =====================================================================
    --  Clock and Reset selection for Read inf of Input buffer and Write inf of Output buffer, CrossbarX selects the Clock signal internally
    -- =====================================================================
    cx_data_inf_clk   <= tsel(CX_USE_CLK_ARB, CX_CLK_ARB  , tsel(CX_USE_CLK2, RX_CLK2, RX_CLK));
    cx_data_inf_reset <= tsel(CX_USE_CLK_ARB, CX_RESET_ARB, RX_RESET);

    -- =====================================================================
    --  Packet length calculation
    -- =====================================================================
    rx_mfb_meta_arr <= slv_array_deser(RX_MFB_META, MFB_REGIONS);

    fr_len_meta_g : for i in MFB_REGIONS-1 downto 0 generate
        rx_mfb_discard_vld(i) <= RX_MFB_DISCARD(i) and RX_MFB_EOF(i);
        fr_len_rx_meta_arr(i) <= rx_mfb_meta_arr(i) & rx_mfb_discard_vld(i);
    end generate;

    fr_len_rx_meta <= slv_array_ser(fr_len_rx_meta_arr);

    mfb_len_cnt_i : entity work.MFB_FRAME_LNG
    generic map(
        REGIONS        => MFB_REGIONS      ,
        REGION_SIZE    => MFB_REGION_SIZE  ,
        BLOCK_SIZE     => MFB_BLOCK_SIZE   ,
        ITEM_WIDTH     => MFB_ITEM_WIDTH   ,
        META_WIDTH     => FR_LEN_META_WIDTH,
        LNG_WIDTH      => log2(PKT_MTU+1)  ,
        REG_BITMAP     => "100"            ,
        IMPLEMENTATION => "parallel"
    )
        port map(
        CLK          => RX_CLK             ,
        RESET        => RX_RESET           ,

        RX_DATA      => RX_MFB_DATA        ,
        RX_META      => fr_len_rx_meta     ,
        RX_SOF       => RX_MFB_SOF         ,
        RX_EOF       => RX_MFB_EOF         ,
        RX_SOF_POS   => RX_MFB_SOF_POS     ,
        RX_EOF_POS   => RX_MFB_EOF_POS     ,
        RX_SRC_RDY   => RX_MFB_SRC_RDY     ,
        RX_DST_RDY   => RX_MFB_DST_RDY     ,

        TX_DATA      => fr_len_tx_data     ,
        TX_META      => fr_len_tx_meta     ,
        TX_FRAME_LNG => fr_len_tx_length   ,
        TX_SOF       => fr_len_tx_sof      ,
        TX_EOF       => fr_len_tx_eof      ,
        TX_SOF_POS   => fr_len_tx_sof_pos  ,
        TX_EOF_POS   => open               ,
        TX_SRC_RDY   => fr_len_tx_src_rdy  ,
        TX_DST_RDY   => fr_len_tx_dst_rdy  ,
        TX_COF       => open               ,
        TX_TEMP_LNG  => open
    );

    -- Note: 1 source 2 destinations situation - Frame length counter is the source,
                                              -- RX buffer is destination 0,
                                              -- Transaction generator is destination 1
    fr_len_tx_dst_rdy <= trgen_mfb_dst_rdy and (not rx_buf_full);

    -- =====================================================================
    --  RX Buffer data writing logic
    -- =====================================================================
    -- FIFOX Multi
    fifoxm_wr_g : for i in MFB_REGIONS-1 downto 0 generate
        rx_buf_ptr_with_discard_arr(i) <= trgen_trans_addr(i) & trgen_trans_discard(i);
        rx_buf_fifoxm_wr           (i) <= trgen_trans_vld(i) and (not rx_buf_fifoxm_full) and (not pacp_rx_pkt_afull(0));
    end generate;

    rx_buf_fifoxm_di <= slv_array_ser(rx_buf_ptr_with_discard_arr);

    fifox_multi_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH          => FIFOXM_DATA_WIDTH,
        ITEMS               => 256              , -- number of ITEMS must be GREATER than UGEN_F_ITEMS (= 32) in CrossbarX
        WRITE_PORTS         => MFB_REGIONS      ,
        READ_PORTS          => MFB_REGIONS      ,
        RAM_TYPE            => "AUTO"           ,
        DEVICE              => DEVICE           ,
        SAFE_READ_MODE      => true
    )
    port map(
        CLK   => RX_CLK                         ,
        RESET => RX_RESET                       ,

        DI     => rx_buf_fifoxm_di              ,
        WR     => rx_buf_fifoxm_wr              ,
        FULL   => rx_buf_fifoxm_full            ,

        DO     => rx_buf_fifoxm_do              ,
        RD     => rx_buf_fifoxm_rd              ,
        EMPTY  => rx_buf_fifoxm_empty
    );

    rx_buf_fifoxm_do_arr <= slv_array_deser(rx_buf_fifoxm_do, MFB_REGIONS);

    fifoxm_rd_data_g : for i in MFB_REGIONS-1 downto 0 generate
        -- For easier orientation:
        -- rx_buf_fifoxm_do_arr : slv_array_t (MFB_REGIONS-1 downto 0)(FIFOXM_DATA_WIDTH-1 downto 0), where
        -- FIFOXM_DATA_WIDTH = RX_BUF_PTR_WIDTH + 1.
        rx_buf_rd_ptr (i) <= unsigned(rx_buf_fifoxm_do_arr(i)(FIFOXM_DATA_WIDTH-1 downto 1));
        rx_buf_discard(i) <= rx_buf_fifoxm_do_arr(i)(0);
    end generate;

    -- FifoX multi read logic
    -- Note: 1 source 2 destinations situation - CX (crox_comp inf) is the source,
                                              -- Fifox Multi (read inf) is destination 0,
                                              -- Asfifox (write inf) is destination 1
    fifox_rd_setup_p : process (all)
        variable pkt_sent_ptr : integer;
    begin
        -- need to map dst_rdy0_fifoxm to CX output - basically a shakedown
        dst_rdy0_remapped <= (others => '0');
        src_rdy0_fifoxm   <= (others => '1');
        pkt_sent_ptr      := 0;
        for i in 0 to MFB_REGIONS-1 loop
            -- there's a valid packet ready at Fifoxm's output
            dst_rdy0_fifoxm(i) <= (not rx_buf_fifoxm_empty(i)) and (not rx_buf_discard(i));
            if (dst_rdy0_fifoxm(i) = '1') then
                dst_rdy0_remapped(pkt_sent_ptr) <= '1';
                src_rdy0_fifoxm(i)              <= dst_rdy1_asfifox and crox_comp_src_rdy(0)(pkt_sent_ptr);
                pkt_sent_ptr                    := pkt_sent_ptr + 1;
            end if;
        end loop;
    end process;

    fifoxm_rd_logic_g : for i in 0 to MFB_REGIONS-1 generate
        rx_buf_fifoxm_rd(i) <= and src_rdy0_fifoxm(i downto 0);
    end generate;

    -- Write pointer logic
    rx_buf_wr_ptr_p : process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            if ((fr_len_tx_src_rdy = '1') and (trgen_mfb_dst_rdy = '1') and (rx_buf_full = '0')) then
                rx_buf_wr_ptr_reg     <= rx_buf_wr_ptr_reg     + 1;
                rx_buf_wr_ptr_inc_reg <= rx_buf_wr_ptr_inc_reg + 1;
            end if;

            if (RX_RESET = '1') then
                rx_buf_wr_ptr_reg     <= to_unsigned(0, log2(RX_BUF_WORDS));
                rx_buf_wr_ptr_inc_reg <= to_unsigned(1, log2(RX_BUF_WORDS));
            end if;
        end if;
    end process;

    -- Read pointer logic
    rx_buf_rd_ptr_p : process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            for i in 0 to MFB_REGIONS-1 loop
                if ((rx_buf_fifoxm_rd(i) = '1') and (rx_buf_fifoxm_empty(i) = '0')) then
                    rx_buf_rd_ptr_reg <= rx_buf_rd_ptr(i);
                end if;
            end loop;

            if (RX_RESET = '1') then
                rx_buf_rd_ptr_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- RX Buffer is full when write pointer reaches read pointer
    rx_buf_full <= '1' when (rx_buf_wr_ptr_inc_reg = resize_right(rx_buf_rd_ptr_reg, log2(RX_BUF_WORDS))) else '0';

    -- Propagate write pointer
    rx_buf_wr_addr <= (others => std_logic_vector(rx_buf_wr_ptr_reg));

    -- =====================================================================
    --  Transaction Generator
    -- =====================================================================
    trgen_mfb_sof_addr <= rx_buf_wr_addr(0);
    trgen_sof_pos_arr_g : for i in 0 to MFB_REGIONS-1 generate
        signal tmp_fr_len_sof_pos : std_logic_vector(max(1, log2(MFB_REGION_SIZE))-1 downto 0);
    begin
        tmp_fr_len_sof_pos       <= fr_len_tx_sof_pos((i+1)*max(1, log2(MFB_REGION_SIZE))-1 downto i*max(1, log2(MFB_REGION_SIZE)));
        trgen_mfb_sof_pos_arr(i) <= std_logic_vector(resize_left(unsigned(tmp_fr_len_sof_pos), log2(MFB_REGION_SIZE)));
    end generate;
    trgen_mfb_sof_vld <= fr_len_tx_sof;

    trgen_mfb_meta_arr   <= slv_array_deser(fr_len_tx_meta  , MFB_REGIONS);
    trgen_mfb_length_arr <= slv_array_deser(fr_len_tx_length, MFB_REGIONS);
    trgen_mfb_eof_vld    <= fr_len_tx_eof;

    trgen_mfb_src_rdy    <= fr_len_tx_src_rdy and (not rx_buf_full);

    trans_gen_i : entity work.CROSSBARX_STREAM_TRANS_GEN
    generic map(
        MFB_REGIONS     => MFB_REGIONS             ,
        MFB_REGION_SIZE => MFB_REGION_SIZE         ,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE          ,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH          ,
        RX_BUF_WORDS    => RX_BUF_WORDS            ,
        PKT_MTU         => PKT_MTU                 ,
        META_WIDTH      => TRGEN_META_WIDTH        ,
        DEVICE          => DEVICE
    )
    port map(
        CLK   => RX_CLK                            ,
        RESET => RX_RESET                          ,

        RX_MFB_SOF_ADDR    => trgen_mfb_sof_addr   ,
        RX_MFB_SOF_POS     => trgen_mfb_sof_pos_arr,
        RX_MFB_SOF_VLD     => trgen_mfb_sof_vld    ,

        RX_MFB_EOF_META    => trgen_mfb_meta_arr   ,
        RX_MFB_EOF_LEN     => trgen_mfb_length_arr ,
        RX_MFB_EOF_VLD     => trgen_mfb_eof_vld    ,

        RX_MFB_SRC_RDY     => trgen_mfb_src_rdy    ,
        RX_MFB_DST_RDY     => trgen_mfb_dst_rdy    ,

        TX_TRANS_A_COL     => trgen_trans_a_col    ,
        TX_TRANS_A_ITEM    => trgen_trans_a_item   ,
        TX_TRANS_META      => trgen_trans_meta_arr ,
        TX_TRANS_LEN       => trgen_trans_len_arr  ,
        TX_TRANS_VLD       => trgen_trans_vld      ,
        TX_TRANS_SRC_RDY   => trgen_trans_src_rdy  ,
        TX_TRANS_DST_RDY   => trgen_trans_dst_rdy
    );

    trgen_trans_dst_rdy <= (not pacp_rx_pkt_afull(0)) and (not rx_buf_fifoxm_full);

    -- =====================================================================
    --  Packet Planner (Gap counter)
    -- =====================================================================
    pacp_rx_g : for i in MFB_REGIONS-1 downto 0 generate
        -- For easier orientation:
        -- trgen_trans_meta_arr : slv_array_t(MFB_REGIONS-1 downto 0)(TRGEN_META_WIDTH-1 downto 0), where
        -- TRGEN_META_WIDTH = MFB_META_WIDTH + 1.
        trgen_trans_mfb_meta(i) <= trgen_trans_meta_arr(i)(TRGEN_META_WIDTH-1 downto 1);
        trgen_trans_discard (i) <= trgen_trans_meta_arr(i)(0);

        trgen_trans_addr    (i) <= trgen_trans_a_col & trgen_trans_a_item(i);
        -- Shifting the RD address of RX Buffer by F_EXTEND_START_SIZE when shrinking packets from the front
        -- By doing this and by using the shortened pkt length, packets from RX Buffer will have the required part cut off from the front
        trgen_trans_addr_mod(i) <= std_logic_vector(signed(trgen_trans_addr(i)) - tsel(F_EXTEND_START_EN and (F_EXTEND_START_SIZE<0), F_EXTEND_START_SIZE, 0));
        pacp_rx_pkt_meta (0)(i) <= trgen_trans_mfb_meta(i) & trgen_trans_addr_mod(i);

        pacp_rx_pkt_len_mod1(0)(i) <= trgen_trans_len_arr(i);
        pacp_rx_pkt_len_mod2(0)(i) <= std_logic_vector(signed(pacp_rx_pkt_len_mod1(0)(i)) + tsel(F_EXTEND_START_EN, F_EXTEND_START_SIZE, 0));
        pacp_rx_pkt_len_mod3(0)(i) <= std_logic_vector(signed(pacp_rx_pkt_len_mod2(0)(i)) + tsel(F_EXTEND_END_EN  , F_EXTEND_END_SIZE  , 0));

        -- When there's a valid transaction at tr_gen's output with discard = '0'
        pacp_rx_pkt_vld(0)(i) <= rx_buf_fifoxm_wr(i) and (not trgen_trans_discard(i));
    end generate;

    -- pre_pp_debug_p : process (RX_CLK)
    -- begin
    --     if (rising_edge(RX_CLK)) then
    --         for i in 0 to MFB_REGIONS-1 loop
    --             if (pacp_rx_pkt_vld(0)(i) = '1') then
    --                 report "Packet's length in Input buffer: " &
    --                        to_string(to_integer(unsigned(trgen_trans_len_arr(i)))) &
    --                        ", its length in Output buffer should be: " &
    --                        to_string(to_integer(unsigned(pacp_rx_pkt_len_mod3(0)(i))))
    --                 severity note;
    --                 report "His address in Input buffer is: " &
    --                        to_string(to_integer(unsigned(trgen_trans_addr(i)))) &
    --                        -- should be same as the address in Input buffer, except when (F_EXTEND_START_EN=true and F_EXTEND_START_SIZE<0)
    --                        " and his modified address is: " &
    --                        to_string(to_integer(unsigned(trgen_trans_addr_mod(i))))
    --                 severity note;
    --             end if;
    --         end loop;
    --     end if;
    -- end process;

    length_checking_p : process (RX_CLK)
    variable pacp_pkt_len_uns : unsigned(log2(PKT_MTU+1)-1 downto 0);
    variable pkt_len_with_gap : natural;
    begin
        if (rising_edge(RX_CLK)) then
            for i in 0 to MFB_REGIONS-1 loop
                if (pacp_rx_pkt_vld(0)(i) = '1') then
                    pacp_pkt_len_uns := unsigned(pacp_rx_pkt_len_mod3(0)(i));
                    pkt_len_with_gap := to_integer(pacp_pkt_len_uns) + GAP_SIZE_MIN + MFB_BLOCK_SIZE-1;
                    assert (pkt_len_with_gap >= MFB_REGION_SIZE*MFB_BLOCK_SIZE)
                        -- 2 SOFs in one Region will occur
                        report "Packet's length + minimal gap size (+ packet alignment) is too small: " &
                                to_string(pkt_len_with_gap) &
                                ", must be at least " &
                                to_string(MFB_REGION_SIZE*MFB_BLOCK_SIZE)
                        severity failure;
                end if;
            end loop;
        end if;
    end process;

    pacp_rx_pkt_src_rdy(0) <= or (pacp_rx_pkt_vld(0));
    pacp_space_rd_ptr      <= std_logic_vector(resize_right(unsigned(tx_buf_rd_ptr_addr), pacp_space_rd_ptr'length));

    pkt_planner_i : entity work.PACKET_PLANNER
    generic map(
        DEVICE            => DEVICE               ,
        STREAMS           => 1                    ,
        PKTS              => MFB_REGIONS          ,
        PLANNED_PKTS      => MFB_REGIONS          ,
        METADATA_WIDTH    => PACP_META_WIDTH      ,
        SPACE_SIZE        => PCAP_SPACE_SIZE      ,
        PKT_SIZE          => PKT_MTU              ,
        GAP_SIZE          => GAP_SIZE_AVG         ,
        GAP_SIZE_MIN      => GAP_SIZE_MIN         ,
        ALIGN             => MFB_BLOCK_SIZE       ,
        FIFO_ITEMS        => 32                   ,
        FIFO_AFULL_OFFSET => 1                    ,
        STREAM_OUT_EN     => true                 ,
        GLOBAL_OUT_EN     => false
    )
    port map(
        CLK   => RX_CLK                           ,
        RESET => RX_RESET                         ,

        RX_STR_PKT_META    => pacp_rx_pkt_meta    ,
        RX_STR_PKT_LEN     => pacp_rx_pkt_len_mod3,
        RX_STR_PKT_VLD     => pacp_rx_pkt_vld     ,
        RX_STR_PKT_SRC_RDY => pacp_rx_pkt_src_rdy ,
        RX_STR_PKT_AFULL   => pacp_rx_pkt_afull   ,

        SPACE_GLB_RD_PTR   => pacp_space_rd_ptr   ,

        TX_STR_PKT_META    => pacp_tx_pkt_meta    ,
        TX_STR_PKT_LEN     => pacp_tx_pkt_len     ,
        TX_STR_PKT_ADDR    => pacp_tx_pkt_addr    ,
        TX_STR_PKT_VLD     => pacp_tx_pkt_vld     ,
        TX_STR_PKT_DST_RDY => pacp_tx_pkt_dst_rdy
    );

    pacp_tx_g : for i in 0 to MFB_REGIONS-1 generate
        -- For easier orientation:
        -- pacp_tx_pkt_meta : slv_array_2d_t(1-1 downto 0)(MFB_REGIONS-1 downto 0)(PACP_META_WIDTH-1 downto 0), where
        -- PACP_META_WIDTH = log2(RX_BUF_WORDS) + log2(BUF_ROWS*MFB_BLOCK_SIZE) + MFB_META_WIDTH.
        pacp_tx_mfb_meta  (i) <= pacp_tx_pkt_meta(0)(i)(PACP_META_WIDTH-1 downto PACP_META_WIDTH-MFB_META_WIDTH);
        pacp_tx_pkt_a_col (i) <= pacp_tx_pkt_meta(0)(i)(log2(TX_BUF_WORDS)+log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto log2(BUF_ROWS*MFB_BLOCK_SIZE));
        pacp_tx_pkt_a_item(i) <= pacp_tx_pkt_meta(0)(i)(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);

        pacp_tx_pkt_len_mod1(i) <= unsigned(pacp_tx_pkt_len(0)(i));
        pacp_tx_pkt_len_mod2(i) <= pacp_tx_pkt_len_mod1(i) - tsel(F_EXTEND_START_EN and (F_EXTEND_START_SIZE>0), F_EXTEND_START_SIZE, 0);
        pacp_tx_pkt_len_mod3(i) <= pacp_tx_pkt_len_mod2(i) - tsel(F_EXTEND_END_EN   and (F_EXTEND_END_SIZE>0)  , F_EXTEND_END_SIZE  , 0);

        pacp_tx_pkt_addr_mod(i) <= std_logic_vector(unsigned(pacp_tx_pkt_addr(0)(i)) + tsel(F_EXTEND_START_EN and (F_EXTEND_START_SIZE>0), F_EXTEND_START_SIZE, 0));
        gapc_trans_b_col    (i) <= pacp_tx_pkt_addr_mod(i)(pacp_tx_pkt_addr_mod(i)'high downto log2(BUF_ROWS*MFB_BLOCK_SIZE));
        gapc_trans_b_item   (i) <= pacp_tx_pkt_addr_mod(i)(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    end generate;

    -- post_pp_debug_p : process (RX_CLK)
    --     variable crox_instr_addr_tmp : std_logic_vector(log2(RX_BUF_WORDS)+log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    -- begin
    --     if (rising_edge(RX_CLK)) then
    --         for i in 0 to MFB_REGIONS-1 loop
    --             crox_instr_addr_tmp := pacp_tx_pkt_a_col(i) & pacp_tx_pkt_a_item(i);
    --             if (pacp_tx_pkt_vld(0)(i) = '1') and (pacp_tx_pkt_dst_rdy(0)(i) = '1') then
    --                 report "CX instruction: Input buffer address is: " &
    --                        to_string(to_integer(unsigned(crox_instr_addr_tmp))) &
    --                        " (" & to_hstring(crox_instr_addr_tmp) & ") "
    --                 severity note;
    --                 report "CX instruction: Output buffer address is: " &
    --                        to_string(to_integer(unsigned(pacp_tx_pkt_addr_mod(i)))) &
    --                        " (" & to_hstring(pacp_tx_pkt_addr_mod(i)) & ") " &
    --                        -- should be same as the address in Input buffer, except when (F_EXTEND_START_EN=true and F_EXTEND_START_SIZE>0)
    --                        ", CX instruction Output buffer address " &
    --                        to_string(to_integer(unsigned(pacp_tx_pkt_addr(0)(i)))) &
    --                        " (" & to_hstring(pacp_tx_pkt_addr(0)(i)) & ") "
    --                 severity note;
    --                 report "CX instr: transferred packet's length is: " &
    --                        to_string(to_integer(unsigned(crox_instr_len(0)(i)))) &
    --                        ", it's length in Output buffer should be: " &
    --                        to_string(to_integer(pacp_tx_pkt_len_mod1(i)))
    --                 severity note;
    --             end if;
    --         end loop;
    --     end if;
    -- end process;

    pacp_rx_pkt_dst_rdy_p : process (all)
    begin
        for i in 0 to MFB_REGIONS-1 loop
            if (pacp_tx_pkt_a_col(i) = pacp_tx_pkt_a_col(0)) then
                pacp_tx_pkt_dst_rdy(0)(i) <= crox_instr_dst_rdy(0);
                gapc_trans_vld        (i) <= pacp_tx_pkt_vld   (0)(i);
            else
                pacp_tx_pkt_dst_rdy(0)(i) <= '0';
                gapc_trans_vld        (i) <= '0';
            end if;
        end loop;
    end process;

    gapc_trans_a_col   <= pacp_tx_pkt_a_col(0);
    gapc_trans_a_item  <= pacp_tx_pkt_a_item;
    gapc_trans_src_rdy <= (or pacp_tx_pkt_vld(0));

    -- =====================================================================
    -- CrossbarX instructions
    -- =====================================================================
    crox_instr_a_col  (0) <= gapc_trans_a_col;
    crox_instr_b_col  (0) <= gapc_trans_b_col;
    crox_instr_vld    (0) <= gapc_trans_vld;
    crox_instr_src_rdy(0) <= gapc_trans_src_rdy;

    crox_instr_item_round_gen : for i in 0 to MFB_REGIONS-1 generate
        crox_instr_a_item(0)(i) <= gapc_trans_a_item(i);
        crox_instr_b_item(0)(i) <= gapc_trans_b_item(i);
        crox_instr_len   (0)(i) <= std_logic_vector(pacp_tx_pkt_len_mod3(i));
    end generate;

    -- =====================================================================
    --  RX Buffer
    -- =====================================================================
    -- pre_ib_debug_p : process (RX_CLK)
    -- begin
    --     if (rising_edge(RX_CLK)) then
    --         for i in BUF_ROWS-1 downto 0 loop
    --             if (rx_buf_wr_en(i) = '1') then
    --                 report "Input buffer write data (" & to_string(i) & "): " &
    --                        to_hstring(rx_buf_wr_data(i)) &
    --                        " and write address: " &
    --                        to_hstring(rx_buf_wr_addr(i))
    --                 severity note;
    --             end if;
    --         end loop;
    --     end if;
    -- end process;

    rx_buf_wr_data <= slv_array_deser(fr_len_tx_data, BUF_ROWS);
    rx_buf_wr_en   <= (others => (fr_len_tx_src_rdy and trgen_mfb_dst_rdy and (not rx_buf_full)));

    input_buffer_gen : for i in 0 to BUF_ROWS-1 generate

        input_buffer_i : entity work.SDP_BRAM_BE
        generic map(
            DATA_WIDTH   => ROW_WIDTH        ,
            ITEMS        => RX_BUF_WORDS     ,
            BLOCK_ENABLE => true             ,
            BLOCK_WIDTH  => MFB_BLOCK_SIZE   ,
            COMMON_CLOCK => RX_BUF_COMMON_CLK,
            OUTPUT_REG   => false            , -- register present in CrossbarX
            DEVICE       => SDP_BRAM_DEVICE
        )
        port map(
            WR_CLK      => RX_CLK            ,
            WR_RST      => RX_RESET          ,
            WR_EN       => rx_buf_wr_en(i)   ,
            WR_BE       => (others => '1')   ,
            WR_ADDR     => rx_buf_wr_addr(i) ,
            WR_DATA     => rx_buf_wr_data(i) ,

            RD_CLK      => cx_data_inf_clk   ,
            RD_RST      => cx_data_inf_reset ,
            RD_EN       => '1'               ,
            RD_PIPE_EN  => '1'               ,
            RD_ADDR     => rx_buf_rd_addr(i) ,
            RD_DATA     => rx_buf_rd_data(i) ,
            RD_DATA_VLD => open
        );

    end generate;

    rx_buf_rd_addr <= crox_src_buf_rd_addr;

    -- =====================================================================
    --  CrossbarX
    -- =====================================================================
    -- pre_cx_debug_p : process (RX_CLK, crox_src_buf_rd_addr)
    -- begin
    --     if rising_edge(RX_CLK) then
    --         for i in BUF_ROWS-1 downto 0 loop
    --             report "CX input data (" & to_string(i) & "): " &
    --                    to_hstring(crox_src_buf_rd_data(i)) &
    --                    " and Input buffer read address: " &
    --                    to_hstring(crox_src_buf_rd_addr(i))
    --             severity note;
    --         end loop;
    --     end if;
    -- end process;

    crox_src_buf_rd_data <= rx_buf_rd_data;

    crox_meta_gen : for i in 0 to MFB_REGIONS-1 generate
        crox_instr_meta(0)(i) <= pacp_tx_mfb_meta   (i)
                               & pacp_tx_pkt_len (0)(i)
                               & pacp_tx_pkt_addr(0)(i);
    end generate;

    crossbarx_i : entity work.CROSSBARX
    generic map(
        DATA_DIR            => true               ,
        USE_CLK2            => CX_USE_CLK2        ,
        USE_CLK_ARB         => CX_USE_CLK_ARB     ,
        BUF_A_COLS          => RX_BUF_WORDS       ,
        BUF_A_STREAM_ROWS   => BUF_ROWS           ,
        BUF_B_COLS          => TX_BUF_WORDS       ,
        BUF_B_ROWS          => BUF_ROWS           ,

        ROW_ITEMS           => MFB_BLOCK_SIZE     ,
        ITEM_WIDTH          => MFB_ITEM_WIDTH     ,
        TRANS_MTU           => PKT_MTU            ,

        METADATA_WIDTH      => CROX_META_WIDTH    ,
        TRANSS              => MFB_REGIONS        ,
        TRANS_FIFO_ITEMS    => TRANS_FIFO_SIZE    ,
        COLOR_TIMEOUT_WIDTH => 6                  ,
        COLOR_CONF_DELAY    => 20                 ,
        RD_LATENCY          => 1                  ,
        TRANS_STREAMS       => 1                  ,
        DATA_MUX_LAT        => 0                  ,
        DATA_MUX_OUTREG_EN  => true               ,
        DATA_ROT_LAT        => 0                  ,
        DATA_ROT_OUTREG_EN  => true               ,
        DEVICE              => DEVICE
    )
    port map(
        CLK       => RX_CLK                       ,
        CLK2      => RX_CLK2                      ,
        RESET     => RX_RESET                     ,
        CLK_ARB   => CX_CLK_ARB                   ,
        RESET_ARB => CX_RESET_ARB                 ,

        TRANS_A_COL        => crox_instr_a_col    ,
        TRANS_A_ITEM       => crox_instr_a_item   ,
        TRANS_B_COL        => crox_instr_b_col    ,
        TRANS_B_ITEM       => crox_instr_b_item   ,
        TRANS_LEN          => crox_instr_len      ,
        TRANS_META         => crox_instr_meta     ,
        TRANS_VLD          => crox_instr_vld      ,
        TRANS_SRC_RDY      => crox_instr_src_rdy  ,
        TRANS_DST_RDY      => crox_instr_dst_rdy  ,

        SRC_BUF_RD_ADDR    => crox_src_buf_rd_addr,
        SRC_BUF_RD_DATA    => crox_src_buf_rd_data,

        DST_BUF_WR_ADDR    => crox_dst_buf_wr_addr,
        DST_BUF_WR_DATA    => crox_dst_buf_wr_data,
        DST_BUF_WR_IE      => crox_dst_buf_wr_ie  ,
        DST_BUF_WR_EN      => crox_dst_buf_wr_en  ,

        TRANS_COMP_META    => crox_comp_meta      ,
        TRANS_COMP_SRC_RDY => crox_comp_src_rdy   ,
        TRANS_COMP_DST_RDY => crox_comp_dst_rdy
    );

    -- post_cx_debug_p : process (RX_CLK)
    -- begin
    --     if (rising_edge(RX_CLK)) then
    --         for i in BUF_ROWS-1 downto 0 loop
    --             if (crox_dst_buf_wr_en(i) = '1') then
    --                 report "CX output data (" & to_string(i) & "): " &
    --                        to_hstring(crox_dst_buf_wr_data(i)) &
    --                        " and Output buffer address: " &
    --                        to_hstring(crox_dst_buf_wr_addr(i))
    --                 severity note;
    --             end if;
    --         end loop;
    --     end if;
    -- end process;

    -- CX meta deserialization (for easier debugging - it is serialized again later)
    crox_comp_meta_g : for i in MFB_REGIONS-1 downto 0 generate
        -- For easier orientation:
        -- crox_comp_meta : slv_array_2d_t(1-1 downto 0)(MFB_REGIONS-1 downto 0)(CROX_META_WIDTH-1 downto 0), where
        -- CROX_META_WIDTH = MFB_META_WIDTH + log2(PKT_MTU+1) + log2(TX_BUF_WORDS*BUF_ROWS*MFB_BLOCK_SIZE).
        crox_comp_mfb_meta(i) <= crox_comp_meta(0)(i)(CROX_META_WIDTH-1 downto CROX_META_WIDTH-MFB_META_WIDTH);
        crox_comp_len     (i) <= crox_comp_meta(0)(i)(CROX_META_WIDTH-MFB_META_WIDTH-1 downto CROX_META_WIDTH-MFB_META_WIDTH-log2(PKT_MTU+1));
        crox_comp_addr    (i) <= crox_comp_meta(0)(i)(log2(TX_BUF_WORDS)+log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    end generate;

    -- (1 source and 2 destinations situation)
    crox_dst_rdy_g : for i in 0 to MFB_REGIONS-1 generate
        crox_comp_dst_rdy(0)(i) <= dst_rdy1_asfifox and dst_rdy0_remapped(i);
    end generate;

    -- =====================================================================
    -- ASFIFOX - because CX and RX_HDR interface of Output buffer run on on different clocks
    -- =====================================================================
    valid_metadata_g : for i in MFB_REGIONS-1 downto 0 generate
        crox_meta_with_vld(i) <= crox_comp_mfb_meta(i) & crox_comp_len(i) & crox_comp_addr(i) & src_rdy1_asfifox(i);
    end generate;
    asfifox_wr_data <= slv_array_ser(crox_meta_with_vld);

    src_rdy1_asfifox_g : for i in MFB_REGIONS-1 downto 0 generate
        -- (1 source and 2 destinations situation)
        src_rdy1_asfifox(i) <= crox_comp_src_rdy(0)(i) and dst_rdy0_remapped(i);
    end generate;
    asfifox_wr_en <= or (src_rdy1_asfifox);

    dst_rdy1_asfifox <= not asfifox_wr_full;

    asfifox_i : entity work.ASFIFOX
    generic map(
        DATA_WIDTH => ASFIFOX_DATA_WIDTH,
        ITEMS      => 32                ,
        RAM_TYPE   => "LUT"             ,
        FWFT_MODE  => true              ,
        OUTPUT_REG => true              ,
        DEVICE     => DEVICE
    )
    port map (
        WR_CLK    => RX_CLK             ,
        WR_RST    => RX_RESET           ,
        WR_DATA   => asfifox_wr_data    ,
        WR_EN     => asfifox_wr_en      ,
        WR_FULL   => asfifox_wr_full    ,
        WR_AFULL  => open               ,
        WR_STATUS => open               ,

        RD_CLK    => TX_CLK             ,
        RD_RST    => TX_RESET           ,
        RD_DATA   => asfifox_rd_data    ,
        RD_EN     => asfifox_rd_en      ,
        RD_EMPTY  => asfifox_rd_empty   ,
        RD_AEMPTY => open               ,
        RD_STATUS => open
    );

    asfifox_rd_data_arr  <= slv_array_deser(asfifox_rd_data, MFB_REGIONS);

    asfifox_rd_en <= tx_buf_rx_instr_dst_rdy;

    -- =====================================================================
    --  TX Buffer
    -- =====================================================================
    crox_comp_gen : for i in 0 to MFB_REGIONS-1 generate
        -- For easier orientation:
        -- asfifox_rd_data_arr : slv_array_t(MFB_REGIONS-1 downto 0)(ASFIFOX_DATA_WIDTH/MFB_REGIONS-1 downto 0), where
        -- ASFIFOX_DATA_WIDTH/MFB_REGIONS-1 = MFB_META_WIDTH + log2(PKT_MTU+1) + log2(TX_BUF_WORDS*BUF_ROWS*MFB_BLOCK_SIZE) + 1.
        tx_buf_rx_instr_meta(i) <= asfifox_rd_data_arr(i)(ASFIFOX_DATA_WIDTH/MFB_REGIONS-1 downto
                                                          ASFIFOX_DATA_WIDTH/MFB_REGIONS-MFB_META_WIDTH);
        tx_buf_rx_instr_len (i) <= asfifox_rd_data_arr(i)(ASFIFOX_DATA_WIDTH/MFB_REGIONS-MFB_META_WIDTH-1 downto
                                                          ASFIFOX_DATA_WIDTH/MFB_REGIONS-MFB_META_WIDTH-log2(PKT_MTU+1));
        tx_buf_rx_instr_addr(i) <= asfifox_rd_data_arr(i)(log2(TX_BUF_WORDS)+log2(BUF_ROWS*MFB_BLOCK_SIZE)+1-1 downto 1);
        tx_buf_rx_instr_vld (i) <= asfifox_rd_data_arr(i)(0);
    end generate;

    tx_buf_rx_instr_src_rdy <= not asfifox_rd_empty;

    tx_buf_wr_data <= crox_dst_buf_wr_data;
    tx_buf_wr_addr <= crox_dst_buf_wr_addr;
    tx_buf_wr_ie   <= crox_dst_buf_wr_ie;
    tx_buf_wr_en   <= crox_dst_buf_wr_en;

    -- pre_obuf_debug_p : process (cx_data_inf_clk)
    --     variable cnt : unsigned(8 downto 0) := (others => '0');
    -- begin
    --     if (rising_edge(cx_data_inf_clk)) then
    --         for i in BUF_ROWS-1 downto 0 loop
    --             if (tx_buf_wr_en(i) = '1') then
    --                 report "Write data to " & to_string(i) & " Buf row of Output buffer: " &
    --                        to_hstring(unsigned(tx_buf_wr_data(i))) &
    --                        " with item enable: " &
    --                        to_hstring(unsigned(tx_buf_wr_ie(i)))
    --                 severity note;
    --                 cnt := cnt + 1;
    --             end if;
    --         end loop;
    --     end if;
    -- end process;

    tx_buffer_i : entity work.MFB_CROSSBARX_OUTPUT_BUFFER
    generic map(
        DEVICE            => DEVICE                    ,
        HDR_META_WIDTH    => 1                         ,
        MVB_ITEMS         => 1                         ,
        MFB_REGIONS       => MFB_REGIONS               ,
        MFB_REGION_SIZE   => MFB_REGION_SIZE           ,
        MFB_BLOCK_SIZE    => MFB_BLOCK_SIZE            ,
        MFB_ITEM_WIDTH    => MFB_ITEM_WIDTH            ,
        MFB_META_WIDTH    => MFB_META_WIDTH            ,
        MFB_META_WITH_SOF => false                     ,
        BUF_BLOCKS        => BUF_ROWS                  ,
        DATA_BLOCK_SIZE   => MFB_BLOCK_SIZE            ,
        DATA_ITEM_WIDTH   => MFB_ITEM_WIDTH            ,
        BUF_WORDS         => TX_BUF_WORDS              ,
        CHANNELS          => 2                         ,
        PKT_SIZE_MAX      => PKT_MTU                   ,
        META_EQ_OUTPUT    => OBUF_META_EQ_OUTPUT       ,
        INPUT_EQ_OUTPUT   => OBUF_INPUT_EQ_OUTPUT
    )
    port map(
        CLK_META          => RX_CLK                    ,
        RESET_META        => RX_RESET                  ,
        CLK_IN            => cx_data_inf_clk           ,
        RESET_IN          => cx_data_inf_reset         ,
        CLK_OUT           => TX_CLK                    ,
        RESET_OUT         => TX_RESET                  ,

        WR_ADDR          => tx_buf_wr_addr             ,
        WR_DATA          => tx_buf_wr_data             ,
        WR_IE            => tx_buf_wr_ie               ,
        WR_EN            => tx_buf_wr_en               ,

        RX_HDR_META      => (others => (others => '0')),
        RX_HDR_MFB_META  => tx_buf_rx_instr_meta       ,
        RX_HDR_CHAN      => (others => (others => '0')),
        RX_HDR_ADDR      => tx_buf_rx_instr_addr       ,
        RX_HDR_LEN       => tx_buf_rx_instr_len        ,
        RX_HDR_VLD       => tx_buf_rx_instr_vld        ,
        RX_HDR_SRC_RDY   => tx_buf_rx_instr_src_rdy    ,
        RX_HDR_DST_RDY   => tx_buf_rx_instr_dst_rdy    ,

        RD_PTR           => tx_buf_rd_ptr_addr         ,

        PKT_SENT_CHAN    => open                       ,
        PKT_SENT_LEN     => open                       ,
        PKT_SENT_SRC_RDY => open                       ,
        PKT_SENT_DST_RDY => '1'                        ,

        TX_MVB_LEN       => open                       ,
        TX_MVB_HDR_META  => open                       ,
        TX_MVB_CHANNEL   => open                       ,
        TX_MVB_VLD       => open                       ,
        TX_MVB_SRC_RDY   => open                       ,
        TX_MVB_DST_RDY   => '1'                        ,

        TX_MFB_DATA      => TX_MFB_DATA                ,
        TX_MFB_META      => TX_MFB_META                ,
        TX_MFB_SOF       => TX_MFB_SOF                 ,
        TX_MFB_EOF       => TX_MFB_EOF                 ,
        TX_MFB_SOF_POS   => TX_MFB_SOF_POS             ,
        TX_MFB_EOF_POS   => TX_MFB_EOF_POS             ,
        TX_MFB_SRC_RDY   => TX_MFB_SRC_RDY             ,
        TX_MFB_DST_RDY   => TX_MFB_DST_RDY
    );

    -- post_obuf_debug_p : process (TX_CLK)
    --     variable cnt : unsigned(8 downto 0) := (others => '0');
    -- begin
    --     if (rising_edge(TX_CLK)) then
    --         if ((TX_MFB_SRC_RDY = '1') and (TX_MFB_DST_RDY = '1')) then
    --             report "Data word number " & to_string(to_integer(cnt)) & ": " &
    --                    to_hstring(TX_MFB_DATA)
    --             severity note;
    --             cnt := cnt + 1;
    --         end if;
    --     end if;
    -- end process;

end architecture;
