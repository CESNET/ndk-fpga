-- connection_block.vhd: PCIe connection block, is need on Intel FPGAs
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity PCIE_CONNECTION_BLOCK is
    generic(
        MFB_REGIONS         : natural := 2;
        MFB_REGION_SIZE     : natural := 1;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 32;
        MFB_UP_META_WIDTH   : natural := 32+128; -- must be 32+128
        MFB_DOWN_META_WIDTH : natural := 3+32+128; -- must be 3+32+128
        -- Depth of FIFO instanced before MTC. For R-Tile only.
        MTC_FIFO_DEPTH      : natural := 512;
        -- Maximum write request (payload) size (in DWORDs)
        PCIE_MPS_DW         : natural := 512/4;
        DEVICE              : string  := "STRATIX10"; -- "STRATIX10" or "AGILEX"
        ENDPOINT_TYPE       : string  := "H_TILE" -- "H_TILE" or "P_TILE" or "R_TILE"
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK               : in  std_logic;
        RESET             : in  std_logic;
        -- =====================================================================
        -- TO/FROM INTEL PCIE HARD IP CORE
        -- =====================================================================
        -- DOWN stream
        RX_AVST_DATA      : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_AVST_HDR       : in  std_logic_vector(MFB_REGIONS*128-1 downto 0); -- not used in H-Tile
        RX_AVST_PREFIX    : in  std_logic_vector(MFB_REGIONS*32-1 downto 0); -- not used in H-Tile
		RX_AVST_SOP       : in  std_logic_vector(MFB_REGIONS-1 downto 0);
		RX_AVST_EOP       : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_AVST_EMPTY     : in  std_logic_vector(MFB_REGIONS*3-1 downto 0);
        RX_AVST_BAR_RANGE : in  std_logic_vector(MFB_REGIONS*3-1 downto 0);
        RX_AVST_VALID     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
		RX_AVST_READY     : out std_logic;
        -- UP stream
        TX_AVST_DATA      : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_AVST_HDR       : out std_logic_vector(MFB_REGIONS*128-1 downto 0); -- not used in H-Tile
        TX_AVST_PREFIX    : out std_logic_vector(MFB_REGIONS*32-1 downto 0); -- not used in H-Tile
		TX_AVST_SOP       : out std_logic_vector(MFB_REGIONS-1 downto 0);
		TX_AVST_EOP       : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_AVST_ERROR     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_AVST_VALID     : out std_logic_vector(MFB_REGIONS-1 downto 0);
		TX_AVST_READY     : in  std_logic;

        -- DOWN stream credits (R-TILE only)
        CRDT_DOWN_INIT_DONE : in  std_logic := '0';
        -- Update valid flags vector (from MSB to LSB: CPLD,NPD,PD,CPLH,NPH,PH)
        CRDT_DOWN_UPDATE    : out std_logic_vector(6-1 downto 0);
        -- Update count of credits
        CRDT_DOWN_CNT_PH    : out std_logic_vector(2-1 downto 0);
        CRDT_DOWN_CNT_NPH   : out std_logic_vector(2-1 downto 0);
        CRDT_DOWN_CNT_CPLH  : out std_logic_vector(2-1 downto 0);
        CRDT_DOWN_CNT_PD    : out std_logic_vector(4-1 downto 0);
        CRDT_DOWN_CNT_NPD   : out std_logic_vector(4-1 downto 0);
        CRDT_DOWN_CNT_CPLD  : out std_logic_vector(4-1 downto 0);

        -- UP stream credits (R-TILE only)
        -- In init phase, the receiver must set the total number of credits
        -- using incremental credit updates. The user logic only receives the
        -- credit updates and waits for CRDT_UP_INIT_DONE to be high.
        CRDT_UP_INIT_DONE : in  std_logic := '0';
        -- Update valid flags vector (from MSB to LSB: CPLD,NPD,PD,CPLH,NPH,PH)
        CRDT_UP_UPDATE    : in  std_logic_vector(6-1 downto 0) := (others => '0');
        -- Update count of credits
        CRDT_UP_CNT_PH    : in  std_logic_vector(2-1 downto 0) := (others => '0');
        CRDT_UP_CNT_NPH   : in  std_logic_vector(2-1 downto 0) := (others => '0');
        CRDT_UP_CNT_CPLH  : in  std_logic_vector(2-1 downto 0) := (others => '0');
        CRDT_UP_CNT_PD    : in  std_logic_vector(4-1 downto 0) := (others => '0');
        CRDT_UP_CNT_NPD   : in  std_logic_vector(4-1 downto 0) := (others => '0');
        CRDT_UP_CNT_CPLD  : in  std_logic_vector(4-1 downto 0) := (others => '0');
        -- =====================================================================
        -- TO/FROM PCIE TRANSACTION CONTROLER (PTC)
        -- =====================================================================
        -- UP stream
        RQ_MFB_DATA       : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RQ_MFB_META       : in  std_logic_vector(MFB_REGIONS*MFB_UP_META_WIDTH-1 downto 0);
        RQ_MFB_SOF        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RQ_MFB_EOF        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RQ_MFB_SOF_POS    : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RQ_MFB_EOF_POS    : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RQ_MFB_SRC_RDY    : in  std_logic;
        RQ_MFB_DST_RDY    : out std_logic;
        -- DOWN stream
        RC_MFB_DATA       : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RC_MFB_META       : out std_logic_vector(MFB_REGIONS*MFB_DOWN_META_WIDTH-1 downto 0);
        RC_MFB_SOF        : out std_logic_vector(MFB_REGIONS-1 downto 0);
        RC_MFB_EOF        : out std_logic_vector(MFB_REGIONS-1 downto 0);
        RC_MFB_SOF_POS    : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RC_MFB_EOF_POS    : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RC_MFB_SRC_RDY    : out std_logic;
        RC_MFB_DST_RDY    : in  std_logic;
        -- =====================================================================
        -- TO/FROM MI32 TRANSACTION CONTROLER (MTC)
        -- =====================================================================
        -- UP stream
        CC_MFB_DATA       : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        CC_MFB_META       : in  std_logic_vector(MFB_REGIONS*MFB_UP_META_WIDTH-1 downto 0);
        CC_MFB_SOF        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        CC_MFB_EOF        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        CC_MFB_SOF_POS    : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        CC_MFB_EOF_POS    : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        CC_MFB_SRC_RDY    : in  std_logic;
        CC_MFB_DST_RDY    : out std_logic;
        -- DOWN stream
        CQ_MFB_DATA       : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        CQ_MFB_META       : out std_logic_vector(MFB_REGIONS*MFB_DOWN_META_WIDTH-1 downto 0);
        CQ_MFB_SOF        : out std_logic_vector(MFB_REGIONS-1 downto 0);
        CQ_MFB_EOF        : out std_logic_vector(MFB_REGIONS-1 downto 0);
        CQ_MFB_SOF_POS    : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        CQ_MFB_EOF_POS    : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        CQ_MFB_SRC_RDY    : out std_logic;
        CQ_MFB_DST_RDY    : in  std_logic
    );
end entity;

architecture FULL of PCIE_CONNECTION_BLOCK is

    constant IS_RTILE_DEVICE        : boolean := ENDPOINT_TYPE="R_TILE";
    constant AVST2MFB_FIFO_DEPTH    : natural := tsel((ENDPOINT_TYPE="H_TILE"),32,512);
    constant AVST2MFB_FIFO_ENABLE   : boolean := not IS_RTILE_DEVICE;
    constant AVST2MFB_FIFO_RAM_TYPE : string  := "AUTO";
    -- latency for H-Tile is 18 cycles (20 cycles for safe)
    -- latency for P-Tile is 27 cycles (30 cycles for safe)
    -- latency for R-Tile is ignored
    constant AVST2MFB_AVST_RDY_LAT  : natural := tsel((ENDPOINT_TYPE="H_TILE"),20,30);
    constant DOWN_USE_DST_RDY       : boolean := True;--TODO (ENDPOINT_TYPE/="R_TILE");
    -- Optimalization parameters
    constant MFB_MERGER_CNT_MAX     : natural := 4;
    constant PIPE_TYPE              : string  := "REG"; -- "SHREG" or "REG"

    signal rx_avst_hdr_arr        : slv_array_t(MFB_REGIONS-1 downto 0)(128-1 downto 0);
    signal rx_avst_prefix_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(32-1 downto 0);
    signal rx_avst_bar_range_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(3-1 downto 0);
    signal rx_avst_meta_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_DOWN_META_WIDTH-1 downto 0);
    signal rx_avst_meta           : std_logic_vector(MFB_REGIONS*MFB_DOWN_META_WIDTH-1 downto 0);
    signal rx_avst_ready_sig      : std_logic;

    signal down_mfb_data          : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal down_mfb_meta          : std_logic_vector(MFB_REGIONS*MFB_DOWN_META_WIDTH-1 downto 0);
    signal down_mfb_sel           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down_mfb_sof           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down_mfb_eof           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down_mfb_eof_pos       : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal down_mfb_src_rdy       : std_logic;
    signal down_mfb_dst_rdy       : std_logic;

    signal down_pipe_mfb_data     : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal down_pipe_mfb_meta     : std_logic_vector(MFB_REGIONS*MFB_DOWN_META_WIDTH-1 downto 0);
    signal down_pipe_mfb_meta_arr : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_DOWN_META_WIDTH-1 downto 0);
    signal down_pipe_mfb_hdr_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(128-1 downto 0);
    signal down_pipe_tlp_type_arr : slv_array_t(MFB_REGIONS-1 downto 0)(8-1 downto 0);
    signal down_pipe_mfb_sel      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down_pipe_mfb_sof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down_pipe_mfb_eof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down_pipe_mfb_eof_pos  : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal down_pipe_mfb_src_rdy  : std_logic;
    signal down_pipe_mfb_dst_rdy  : std_logic;

    signal down0_mfb_data         : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal down0_mfb_meta         : std_logic_vector(MFB_REGIONS*MFB_DOWN_META_WIDTH-1 downto 0);
    signal down0_mfb_sof          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down0_mfb_eof          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down0_mfb_eof_pos      : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal down0_mfb_src_rdy      : std_logic;
    signal down0_mfb_dst_rdy      : std_logic;

    signal down0_pipe_mfb_data    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal down0_pipe_mfb_meta    : std_logic_vector(MFB_REGIONS*MFB_DOWN_META_WIDTH-1 downto 0);
    signal down0_pipe_mfb_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down0_pipe_mfb_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down0_pipe_mfb_eof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal down0_pipe_mfb_src_rdy : std_logic;
    signal down0_pipe_mfb_dst_rdy : std_logic;

    signal down0_pipe_mfb_meta_arr : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_DOWN_META_WIDTH-1 downto 0);
    signal down0_pipe_tlp_type_lv  : slv_array_t(MFB_REGIONS downto 0)(8-1 downto 0);
    signal down0_pipe_tlp_len_lv   : slv_array_t(MFB_REGIONS downto 0)(10-1 downto 0);
    signal down0_pipe_tlp_vld      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal crdt_down_update_mtc    : std_logic_vector(6-1 downto 0);

    signal down1_mfb_data         : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal down1_mfb_meta         : std_logic_vector(MFB_REGIONS*MFB_DOWN_META_WIDTH-1 downto 0);
    signal down1_mfb_sof          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down1_mfb_eof          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down1_mfb_eof_pos      : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal down1_mfb_src_rdy      : std_logic;
    signal down1_mfb_dst_rdy      : std_logic;

    signal down1_pipe_mfb_data    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal down1_pipe_mfb_meta    : std_logic_vector(MFB_REGIONS*MFB_DOWN_META_WIDTH-1 downto 0);
    signal down1_pipe_mfb_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down1_pipe_mfb_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal down1_pipe_mfb_eof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal down1_pipe_mfb_src_rdy : std_logic;
    signal down1_pipe_mfb_dst_rdy : std_logic;

    signal down1_pipe_mfb_meta_arr : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_DOWN_META_WIDTH-1 downto 0);
    signal down1_pipe_tlp_type_lv  : slv_array_t(MFB_REGIONS downto 0)(8-1 downto 0);
    signal down1_pipe_tlp_len_lv   : slv_array_t(MFB_REGIONS downto 0)(10-1 downto 0);
    signal down1_pipe_tlp_vld      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal crdt_down_update_ptc    : std_logic_vector(6-1 downto 0);

    signal up0_mfb_data           : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal up0_mfb_meta           : std_logic_vector(MFB_REGIONS*MFB_UP_META_WIDTH-1 downto 0);
    signal up0_mfb_sof            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up0_mfb_eof            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up0_mfb_src_rdy        : std_logic;
    signal up0_mfb_dst_rdy        : std_logic;

    signal up0_pipe_mfb_data      : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal up0_pipe_mfb_meta      : std_logic_vector(MFB_REGIONS*MFB_UP_META_WIDTH-1 downto 0);
    signal up0_pipe_mfb_sof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up0_pipe_mfb_eof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up0_pipe_mfb_src_rdy   : std_logic;
    signal up0_pipe_mfb_dst_rdy   : std_logic;
    signal up0_pipe_mfb_src_rdy_2 : std_logic;
    signal up0_pipe_mfb_dst_rdy_2 : std_logic;

    signal up0_pipe_mfb_meta_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_UP_META_WIDTH-1 downto 0);
    signal up0_pipe_tlp_type_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(8-1 downto 0);
    signal up0_pipe_tlp_len_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(10-1 downto 0);
    signal up0_pipe_tlp_vld       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up0_pipe_crdt_ok       : std_logic;

    signal up1_mfb_data           : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal up1_mfb_meta           : std_logic_vector(MFB_REGIONS*MFB_UP_META_WIDTH-1 downto 0);
    signal up1_mfb_sof            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up1_mfb_eof            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up1_mfb_src_rdy        : std_logic;
    signal up1_mfb_dst_rdy        : std_logic;

    signal up1_pipe_mfb_data      : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal up1_pipe_mfb_meta      : std_logic_vector(MFB_REGIONS*MFB_UP_META_WIDTH-1 downto 0);
    signal up1_pipe_mfb_sof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up1_pipe_mfb_eof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up1_pipe_mfb_src_rdy   : std_logic;
    signal up1_pipe_mfb_dst_rdy   : std_logic;
    signal up1_pipe_mfb_src_rdy_2 : std_logic;
    signal up1_pipe_mfb_dst_rdy_2 : std_logic;

    signal up1_pipe_mfb_meta_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_UP_META_WIDTH-1 downto 0);
    signal up1_pipe_tlp_type_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(8-1 downto 0);
    signal up1_pipe_tlp_len_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(10-1 downto 0);
    signal up1_pipe_tlp_vld       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up1_pipe_crdt_ok       : std_logic;

    signal up_mfb_data            : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal up_mfb_meta            : std_logic_vector(MFB_REGIONS*MFB_UP_META_WIDTH-1 downto 0);
    signal up_mfb_sof             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up_mfb_eof             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up_mfb_src_rdy         : std_logic;
    signal up_mfb_dst_rdy         : std_logic;

    signal up_pipe_mfb_data       : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal up_pipe_mfb_meta       : std_logic_vector(MFB_REGIONS*MFB_UP_META_WIDTH-1 downto 0);
    signal up_pipe_mfb_sof        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up_pipe_mfb_eof        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal up_pipe_mfb_src_rdy    : std_logic;
    signal up_pipe_mfb_dst_rdy    : std_logic;

    signal tx_avst_meta           : std_logic_vector(MFB_REGIONS*MFB_UP_META_WIDTH-1 downto 0);
    signal tx_avst_meta_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_UP_META_WIDTH-1 downto 0);
    signal tx_avst_hdr_arr        : slv_array_t(MFB_REGIONS-1 downto 0)(128-1 downto 0);
    signal tx_avst_prefix_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(32-1 downto 0);

    signal tx_inc_frame                : std_logic_vector(MFB_REGIONS+1-1 downto 0);
    signal tx_gap_inside_frame_dbg     : std_logic;
    signal tx_gap_inside_frame_dbg_reg : std_logic;

    attribute preserve_for_debug : boolean;
    attribute preserve_for_debug of tx_gap_inside_frame_dbg_reg : signal is true;

begin

    -- =========================================================================
    --  DOWN STREAM
    -- =========================================================================

    rx_avst_hdr_arr       <= slv_array_downto_deser(RX_AVST_HDR,MFB_REGIONS,128);
    rx_avst_prefix_arr    <= slv_array_downto_deser(RX_AVST_PREFIX,MFB_REGIONS,32);
    rx_avst_bar_range_arr <= slv_array_downto_deser(RX_AVST_BAR_RANGE,MFB_REGIONS,3);

    rx_avst_meta_arr_g : for i in 0 to MFB_REGIONS-1 generate
        rx_avst_meta_arr(i) <= rx_avst_bar_range_arr(i) & rx_avst_prefix_arr(i) &
            rx_avst_hdr_arr(i)(32-1 downto 0)  & rx_avst_hdr_arr(i)(64-1 downto 32) &
            rx_avst_hdr_arr(i)(96-1 downto 64) & rx_avst_hdr_arr(i)(128-1 downto 96);
    end generate;

    rx_avst_meta <= slv_array_ser(rx_avst_meta_arr,MFB_REGIONS,MFB_DOWN_META_WIDTH);

    -- conversion AVST2MFB
    avst2mfb_i : entity work.PCIE_AVST2MFB
    generic map(
        REGIONS            => MFB_REGIONS,
        REGION_SIZE        => MFB_REGION_SIZE,
        BLOCK_SIZE         => MFB_BLOCK_SIZE,
        ITEM_WIDTH         => MFB_ITEM_WIDTH,
        META_WIDTH         => MFB_DOWN_META_WIDTH,
        AVALON_RDY_LATENCY => AVST2MFB_AVST_RDY_LAT,
        FIFO_DEPTH         => AVST2MFB_FIFO_DEPTH,
        FIFO_ENABLE        => AVST2MFB_FIFO_ENABLE,
        FIFO_RAM_TYPE      => AVST2MFB_FIFO_RAM_TYPE,
        DEVICE             => DEVICE
    )
    port map(
        CLK            => CLK,
        RST            => RESET,

        RX_AVST_DATA   => RX_AVST_DATA,
        RX_AVST_META   => rx_avst_meta,
        RX_AVST_SOP    => RX_AVST_SOP,
        RX_AVST_EOP    => RX_AVST_EOP,
        RX_AVST_EMPTY  => RX_AVST_EMPTY,
        RX_AVST_VALID  => RX_AVST_VALID,
        RX_AVST_READY  => rx_avst_ready_sig,

        TX_MFB_DATA    => down_mfb_data,
        TX_MFB_META    => down_mfb_meta,
        TX_MFB_SOF     => down_mfb_sof,
        TX_MFB_EOF     => down_mfb_eof,
        TX_MFB_EOF_POS => down_mfb_eof_pos,
        TX_MFB_SRC_RDY => down_mfb_src_rdy,
        TX_MFB_DST_RDY => down_mfb_dst_rdy
    );

    rx_avst_ready_g : if (ENDPOINT_TYPE = "R_TILE") generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                RX_AVST_READY <= CRDT_DOWN_INIT_DONE;
                if (RESET = '1') then
                    RX_AVST_READY <= '0';
                end if;
            end if;
        end process;
    else generate
        RX_AVST_READY <= rx_avst_ready_sig;
    end generate;

    down_mfb_pipe_i : entity work.MFB_PIPE
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => MFB_DOWN_META_WIDTH,
        FAKE_PIPE   => false,
        USE_DST_RDY => DOWN_USE_DST_RDY,
        PIPE_TYPE   => PIPE_TYPE,
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => down_mfb_data,
        RX_META    => down_mfb_meta,
        RX_SOF_POS => (others => '0'),
        RX_EOF_POS => down_mfb_eof_pos,
        RX_SOF     => down_mfb_sof,
        RX_EOF     => down_mfb_eof,
        RX_SRC_RDY => down_mfb_src_rdy,
        RX_DST_RDY => down_mfb_dst_rdy,

        TX_DATA    => down_pipe_mfb_data,
        TX_META    => down_pipe_mfb_meta,
        TX_SOF_POS => open,
        TX_EOF_POS => down_pipe_mfb_eof_pos,
        TX_SOF     => down_pipe_mfb_sof,
        TX_EOF     => down_pipe_mfb_eof,
        TX_SRC_RDY => down_pipe_mfb_src_rdy,
        TX_DST_RDY => down_pipe_mfb_dst_rdy
    );

    down_pipe_mfb_meta_arr <= slv_array_downto_deser(down_pipe_mfb_meta,MFB_REGIONS,MFB_DOWN_META_WIDTH);

    down1_pipe_mfb_meta_arr_unpack_g : for i in 0 to MFB_REGIONS-1 generate
        down_pipe_mfb_hdr_arr(i) <= down_pipe_mfb_meta_arr(i)(128-1 downto 0);
    end generate;

    tlp_type_h_tile_g : if ENDPOINT_TYPE = "H_TILE" generate
        down_pipe_tlp_type_arr_g : for i in 0 to MFB_REGIONS-1 generate
            down_pipe_tlp_type_arr(i) <= down_pipe_mfb_data(i*256+31 downto i*256+24);
        end generate;
    end generate;

    tlp_type_p_tile_g : if ENDPOINT_TYPE = "P_TILE" or ENDPOINT_TYPE = "R_TILE" generate
        down_pipe_tlp_type_arr_g : for i in 0 to MFB_REGIONS-1 generate
            down_pipe_tlp_type_arr(i) <= down_pipe_mfb_hdr_arr(i)(31 downto 24);
        end generate;
    end generate;

    down_mfb_sel_g : for i in 0 to MFB_REGIONS-1 generate
        with down_pipe_tlp_type_arr(i) select
        down_pipe_mfb_sel(i) <= '1' when "00001010", -- Completion without Data
                                '1' when "01001010", -- Completion with Data
                                '1' when "00001011", -- Completion for Locked Memory Read without Data
                                '1' when "01001011", -- Completion for Locked Memory Read
                                '0' when others;
    end generate;

    -- MFB splitter
    mfb_splitter_i : entity work.MFB_SPLITTER_SIMPLE
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => MFB_DOWN_META_WIDTH
    )
    port map(
        CLK             => CLK,
        RST             => RESET,

        RX_MFB_SEL      => down_pipe_mfb_sel,
        RX_MFB_DATA     => down_pipe_mfb_data,
        RX_MFB_META     => down_pipe_mfb_meta,
        RX_MFB_SOF      => down_pipe_mfb_sof,
        RX_MFB_EOF      => down_pipe_mfb_eof,
        RX_MFB_SOF_POS  => (others => '0'),
        RX_MFB_EOF_POS  => down_pipe_mfb_eof_pos,
        RX_MFB_SRC_RDY  => down_pipe_mfb_src_rdy,
        RX_MFB_DST_RDY  => down_pipe_mfb_dst_rdy,

        TX0_MFB_DATA    => down0_mfb_data,
        TX0_MFB_META    => down0_mfb_meta,
        TX0_MFB_SOF     => down0_mfb_sof,
        TX0_MFB_EOF     => down0_mfb_eof,
        TX0_MFB_SOF_POS => open,
        TX0_MFB_EOF_POS => down0_mfb_eof_pos,
        TX0_MFB_SRC_RDY => down0_mfb_src_rdy,
        TX0_MFB_DST_RDY => down0_mfb_dst_rdy,

        TX1_MFB_DATA    => down1_mfb_data,
        TX1_MFB_META    => down1_mfb_meta,
        TX1_MFB_SOF     => down1_mfb_sof,
        TX1_MFB_EOF     => down1_mfb_eof,
        TX1_MFB_SOF_POS => open,
        TX1_MFB_EOF_POS => down1_mfb_eof_pos,
        TX1_MFB_SRC_RDY => down1_mfb_src_rdy,
        TX1_MFB_DST_RDY => down1_mfb_dst_rdy
    );

    down0_pipe_g: if not IS_RTILE_DEVICE generate
        down0_mfb_pipe_i : entity work.MFB_PIPE
        generic map(
            REGIONS     => MFB_REGIONS,
            REGION_SIZE => MFB_REGION_SIZE,
            BLOCK_SIZE  => MFB_BLOCK_SIZE,
            ITEM_WIDTH  => MFB_ITEM_WIDTH,
            META_WIDTH  => MFB_DOWN_META_WIDTH,
            FAKE_PIPE   => false,
            USE_DST_RDY => DOWN_USE_DST_RDY,
            PIPE_TYPE   => PIPE_TYPE,
            DEVICE      => DEVICE
        )
        port map(
            CLK        => CLK,
            RESET      => RESET,

            RX_DATA    => down0_mfb_data,
            RX_META    => down0_mfb_meta,
            RX_SOF_POS => (others => '0'),
            RX_EOF_POS => down0_mfb_eof_pos,
            RX_SOF     => down0_mfb_sof,
            RX_EOF     => down0_mfb_eof,
            RX_SRC_RDY => down0_mfb_src_rdy,
            RX_DST_RDY => down0_mfb_dst_rdy,

            TX_DATA    => down0_pipe_mfb_data,
            TX_META    => down0_pipe_mfb_meta,
            TX_SOF_POS => open,
            TX_EOF_POS => down0_pipe_mfb_eof_pos,
            TX_SOF     => down0_pipe_mfb_sof,
            TX_EOF     => down0_pipe_mfb_eof,
            TX_SRC_RDY => down0_pipe_mfb_src_rdy,
            TX_DST_RDY => down0_pipe_mfb_dst_rdy
        );
    end generate;

    down0_fifo_g: if IS_RTILE_DEVICE generate
        down0_mfb_fifo_i : entity work.MFB_FIFOX
        generic map(
            REGIONS     => MFB_REGIONS,
            REGION_SIZE => MFB_REGION_SIZE,
            BLOCK_SIZE  => MFB_BLOCK_SIZE,
            ITEM_WIDTH  => MFB_ITEM_WIDTH,
            META_WIDTH  => MFB_DOWN_META_WIDTH,
            FIFO_DEPTH  => MTC_FIFO_DEPTH,
            DEVICE      => DEVICE
        )
        port map(
            CLK        => CLK,
            RST        => RESET,

            RX_DATA    => down0_mfb_data,
            RX_META    => down0_mfb_meta,
            RX_SOF_POS => (others => '0'),
            RX_EOF_POS => down0_mfb_eof_pos,
            RX_SOF     => down0_mfb_sof,
            RX_EOF     => down0_mfb_eof,
            RX_SRC_RDY => down0_mfb_src_rdy,
            RX_DST_RDY => down0_mfb_dst_rdy,

            TX_DATA    => down0_pipe_mfb_data,
            TX_META    => down0_pipe_mfb_meta,
            TX_SOF_POS => open,
            TX_EOF_POS => down0_pipe_mfb_eof_pos,
            TX_SOF     => down0_pipe_mfb_sof,
            TX_EOF     => down0_pipe_mfb_eof,
            TX_SRC_RDY => down0_pipe_mfb_src_rdy,
            TX_DST_RDY => down0_pipe_mfb_dst_rdy
        );
    end generate;

    down0_pipe_mfb_meta_arr <= slv_array_downto_deser(down0_pipe_mfb_meta,MFB_REGIONS,MFB_DOWN_META_WIDTH);

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (down0_pipe_mfb_dst_rdy = '1') then
                down0_pipe_tlp_type_lv(0) <= down0_pipe_tlp_type_lv(MFB_REGIONS);
                down0_pipe_tlp_len_lv(0)  <= down0_pipe_tlp_len_lv(MFB_REGIONS);
            end if;
        end if;
    end process;

    down0_pipe_tlp_g: for i in 0 to MFB_REGIONS-1 generate
        process (all)
        begin
            if (down0_pipe_mfb_src_rdy = '1' and down0_pipe_mfb_sof(i) = '1') then
                if (ENDPOINT_TYPE = "H_TILE") then
                    down0_pipe_tlp_type_lv(i+1) <= down0_pipe_mfb_data(i*256+31 downto i*256+24);
                    down0_pipe_tlp_len_lv(i+1)  <= down0_pipe_mfb_data(i*256+9 downto i*256);
                else -- ENDPOINT_TYPE = "P_TILE" or ENDPOINT_TYPE = "R_TILE"
                    down0_pipe_tlp_type_lv(i+1) <= down0_pipe_mfb_meta_arr(i)(31 downto 24);
                    down0_pipe_tlp_len_lv(i+1)  <= down0_pipe_mfb_meta_arr(i)(9 downto 0);
                end if;
            else
                down0_pipe_tlp_type_lv(i+1) <= down0_pipe_tlp_type_lv(i);
                down0_pipe_tlp_len_lv(i+1)  <= down0_pipe_tlp_len_lv(i);
            end if;
        end process;
    end generate;

    down0_pipe_tlp_vld <= down0_pipe_mfb_src_rdy and down0_pipe_mfb_dst_rdy and down0_pipe_mfb_eof;

    crdt_down_mtc_i : entity work.CB_RTILE_CRDT_DOWN
    generic map(
        REGIONS          => MFB_REGIONS,
        CRDT_ENABLE      => IS_RTILE_DEVICE
    )
    port map(
        CLK            => CLK,
        RESET          => RESET,

        TLP_FMT_TYPE   => down0_pipe_tlp_type_lv(MFB_REGIONS downto 1),
        TLP_LENGTH     => down0_pipe_tlp_len_lv(MFB_REGIONS downto 1),
        TLP_VALID      => down0_pipe_tlp_vld,

        CRDT_INIT_DONE => CRDT_DOWN_INIT_DONE,
        CRDT_UPDATE    => crdt_down_update_mtc,
        CRDT_CNT_PH    => CRDT_DOWN_CNT_PH,
        CRDT_CNT_NPH   => CRDT_DOWN_CNT_NPH,
        CRDT_CNT_CPLH  => open,
        CRDT_CNT_PD    => CRDT_DOWN_CNT_PD,
        CRDT_CNT_NPD   => CRDT_DOWN_CNT_NPD,
        CRDT_CNT_CPLD  => open
    );

    CRDT_DOWN_UPDATE(0) <= crdt_down_update_mtc(0);
    CRDT_DOWN_UPDATE(1) <= crdt_down_update_mtc(1);
    CRDT_DOWN_UPDATE(3) <= crdt_down_update_mtc(3);
    CRDT_DOWN_UPDATE(4) <= crdt_down_update_mtc(4);

    -- DOWN stream to MTC
    CQ_MFB_DATA            <= down0_pipe_mfb_data;
    CQ_MFB_META            <= down0_pipe_mfb_meta;
    CQ_MFB_SOF             <= down0_pipe_mfb_sof;
    CQ_MFB_EOF             <= down0_pipe_mfb_eof;
    CQ_MFB_SOF_POS         <= (others => '0');
    CQ_MFB_EOF_POS         <= down0_pipe_mfb_eof_pos;
    CQ_MFB_SRC_RDY         <= down0_pipe_mfb_src_rdy;
    down0_pipe_mfb_dst_rdy <= CQ_MFB_DST_RDY;

    down1_mfb_pipe_i : entity work.MFB_PIPE
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => MFB_DOWN_META_WIDTH,
        FAKE_PIPE   => false,
        USE_DST_RDY => DOWN_USE_DST_RDY,
        PIPE_TYPE   => PIPE_TYPE,
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => down1_mfb_data,
        RX_META    => down1_mfb_meta,
        RX_SOF_POS => (others => '0'),
        RX_EOF_POS => down1_mfb_eof_pos,
        RX_SOF     => down1_mfb_sof,
        RX_EOF     => down1_mfb_eof,
        RX_SRC_RDY => down1_mfb_src_rdy,
        RX_DST_RDY => down1_mfb_dst_rdy,

        TX_DATA    => down1_pipe_mfb_data,
        TX_META    => down1_pipe_mfb_meta,
        TX_SOF_POS => open,
        TX_EOF_POS => down1_pipe_mfb_eof_pos,
        TX_SOF     => down1_pipe_mfb_sof,
        TX_EOF     => down1_pipe_mfb_eof,
        TX_SRC_RDY => down1_pipe_mfb_src_rdy,
        TX_DST_RDY => down1_pipe_mfb_dst_rdy
    );

    down1_pipe_mfb_meta_arr <= slv_array_downto_deser(down1_pipe_mfb_meta,MFB_REGIONS,MFB_DOWN_META_WIDTH);

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (down1_pipe_mfb_dst_rdy = '1') then
                down1_pipe_tlp_type_lv(0) <= down1_pipe_tlp_type_lv(MFB_REGIONS);
                down1_pipe_tlp_len_lv(0)  <= down1_pipe_tlp_len_lv(MFB_REGIONS);
            end if;
        end if;
    end process;

    down1_pipe_tlp_g: for i in 0 to MFB_REGIONS-1 generate
        process (all)
        begin
            if (down1_pipe_mfb_src_rdy = '1' and down1_pipe_mfb_sof(i) = '1') then
                if (ENDPOINT_TYPE = "H_TILE") then
                    down1_pipe_tlp_type_lv(i+1) <= down1_pipe_mfb_data(i*256+31 downto i*256+24);
                    down1_pipe_tlp_len_lv(i+1)  <= down1_pipe_mfb_data(i*256+9 downto i*256);
                else -- ENDPOINT_TYPE = "P_TILE" or ENDPOINT_TYPE = "R_TILE"
                    down1_pipe_tlp_type_lv(i+1) <= down1_pipe_mfb_meta_arr(i)(31 downto 24);
                    down1_pipe_tlp_len_lv(i+1)  <= down1_pipe_mfb_meta_arr(i)(9 downto 0);
                end if;
            else
                down1_pipe_tlp_type_lv(i+1) <= down1_pipe_tlp_type_lv(i);
                down1_pipe_tlp_len_lv(i+1)  <= down1_pipe_tlp_len_lv(i);
            end if;
        end process;
    end generate;

    down1_pipe_tlp_vld <= down1_pipe_mfb_src_rdy and down1_pipe_mfb_dst_rdy and down1_pipe_mfb_eof;

    crdt_down_ptc_i : entity work.CB_RTILE_CRDT_DOWN
    generic map(
        REGIONS          => MFB_REGIONS,
        CRDT_ENABLE      => IS_RTILE_DEVICE
    )
    port map(
        CLK            => CLK,
        RESET          => RESET,

        TLP_FMT_TYPE   => down1_pipe_tlp_type_lv(MFB_REGIONS downto 1),
        TLP_LENGTH     => down1_pipe_tlp_len_lv(MFB_REGIONS downto 1),
        TLP_VALID      => down1_pipe_tlp_vld,

        CRDT_INIT_DONE => CRDT_DOWN_INIT_DONE,
        CRDT_UPDATE    => crdt_down_update_ptc,
        CRDT_CNT_PH    => open,
        CRDT_CNT_NPH   => open,
        CRDT_CNT_CPLH  => CRDT_DOWN_CNT_CPLH,
        CRDT_CNT_PD    => open,
        CRDT_CNT_NPD   => open,
        CRDT_CNT_CPLD  => CRDT_DOWN_CNT_CPLD
    );

    CRDT_DOWN_UPDATE(2) <= crdt_down_update_ptc(2);
    CRDT_DOWN_UPDATE(5) <= crdt_down_update_ptc(5);

    -- DOWN stream to PTC
    RC_MFB_DATA            <= down1_pipe_mfb_data;
    RC_MFB_META            <= down1_pipe_mfb_meta;
    RC_MFB_SOF             <= down1_pipe_mfb_sof;
    RC_MFB_EOF             <= down1_pipe_mfb_eof;
    RC_MFB_SOF_POS         <= (others => '0');
    RC_MFB_EOF_POS         <= down1_pipe_mfb_eof_pos;
    RC_MFB_SRC_RDY         <= down1_pipe_mfb_src_rdy;
    down1_pipe_mfb_dst_rdy <= RC_MFB_DST_RDY;

    -- =========================================================================
    --  UP STREAM
    -- =========================================================================

    -- UP stream from MTC
    up0_mfb_data    <= CC_MFB_DATA;
    up0_mfb_meta    <= CC_MFB_META;
    up0_mfb_sof     <= CC_MFB_SOF;
    up0_mfb_eof     <= CC_MFB_EOF;
    up0_mfb_src_rdy <= CC_MFB_SRC_RDY;
    CC_MFB_DST_RDY  <= up0_mfb_dst_rdy;

    up0_mfb_pipe_i : entity work.MFB_PIPE
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => MFB_UP_META_WIDTH,
        FAKE_PIPE   => false,
        USE_DST_RDY => true,
        PIPE_TYPE   => PIPE_TYPE,
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => up0_mfb_data,
        RX_META    => up0_mfb_meta,
        RX_SOF_POS => (others => '0'),
        RX_EOF_POS => (others => '0'),
        RX_SOF     => up0_mfb_sof,
        RX_EOF     => up0_mfb_eof,
        RX_SRC_RDY => up0_mfb_src_rdy,
        RX_DST_RDY => up0_mfb_dst_rdy,

        TX_DATA    => up0_pipe_mfb_data,
        TX_META    => up0_pipe_mfb_meta,
        TX_SOF_POS => open,
        TX_EOF_POS => open,
        TX_SOF     => up0_pipe_mfb_sof,
        TX_EOF     => up0_pipe_mfb_eof,
        TX_SRC_RDY => up0_pipe_mfb_src_rdy,
        TX_DST_RDY => up0_pipe_mfb_dst_rdy
    );

    up0_pipe_mfb_meta_arr <= slv_array_downto_deser(up0_pipe_mfb_meta,MFB_REGIONS,MFB_UP_META_WIDTH);

    up0_tlp_type_h_tile_g : if ENDPOINT_TYPE = "H_TILE" generate
        arr_g : for i in 0 to MFB_REGIONS-1 generate
            up0_pipe_tlp_type_arr(i) <= up0_pipe_mfb_data(i*256+31 downto i*256+24);
            up0_pipe_tlp_len_arr(i)  <= up0_pipe_mfb_data(i*256+9 downto i*256);
        end generate;
    end generate;

    up0_tlp_type_p_tile_g : if ENDPOINT_TYPE = "P_TILE" or ENDPOINT_TYPE = "R_TILE" generate
        arr_g : for i in 0 to MFB_REGIONS-1 generate
            up0_pipe_tlp_type_arr(i) <= up0_pipe_mfb_meta_arr(i)(31 downto 24);
            up0_pipe_tlp_len_arr(i)  <= up0_pipe_mfb_meta_arr(i)(9 downto 0);
        end generate;
    end generate;

    up0_pipe_tlp_vld <= up0_pipe_mfb_src_rdy and up0_pipe_mfb_sof;

    crdt_up_mtc_i : entity work.CB_RTILE_CRDT_UP
    generic map(
        REGIONS     => MFB_REGIONS,
        CRDT_ENABLE => False,
        PCIE_MPS_DW => PCIE_MPS_DW
    )
    port map(
        CLK            => CLK,
        RESET          => RESET,

        CRDT_INIT_DONE => CRDT_UP_INIT_DONE,
        CRDT_UPDATE    => CRDT_UP_UPDATE,
        CRDT_CNT_PH    => (others => '0'),
        CRDT_CNT_NPH   => (others => '0'),
        CRDT_CNT_CPLH  => CRDT_UP_CNT_CPLH,
        CRDT_CNT_PD    => (others => '0'),
        CRDT_CNT_NPD   => (others => '0'),
        CRDT_CNT_CPLD  => CRDT_UP_CNT_CPLD,

        TLP_FMT_TYPE   => up0_pipe_tlp_type_arr,
        TLP_LENGTH     => up0_pipe_tlp_len_arr,
        TLP_HDR_VLD    => up0_pipe_tlp_vld,
        TLP_CRDT_OK    => up0_pipe_crdt_ok,
        READY          => up0_pipe_mfb_dst_rdy_2
    );

    up0_pipe_mfb_src_rdy_2 <= up0_pipe_mfb_src_rdy and up0_pipe_crdt_ok;
    up0_pipe_mfb_dst_rdy   <= up0_pipe_mfb_dst_rdy_2 and up0_pipe_crdt_ok;

    -- UP stream from PTC
    up1_mfb_data    <= RQ_MFB_DATA;
    up1_mfb_meta    <= RQ_MFB_META;
    up1_mfb_sof     <= RQ_MFB_SOF;
    up1_mfb_eof     <= RQ_MFB_EOF;
    up1_mfb_src_rdy <= RQ_MFB_SRC_RDY;
    RQ_MFB_DST_RDY  <= up1_mfb_dst_rdy;

    up1_mfb_pipe_i : entity work.MFB_PIPE
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => MFB_UP_META_WIDTH,
        FAKE_PIPE   => false,
        USE_DST_RDY => true,
        PIPE_TYPE   => PIPE_TYPE,
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => up1_mfb_data,
        RX_META    => up1_mfb_meta,
        RX_SOF_POS => (others => '0'),
        RX_EOF_POS => (others => '0'),
        RX_SOF     => up1_mfb_sof,
        RX_EOF     => up1_mfb_eof,
        RX_SRC_RDY => up1_mfb_src_rdy,
        RX_DST_RDY => up1_mfb_dst_rdy,

        TX_DATA    => up1_pipe_mfb_data,
        TX_META    => up1_pipe_mfb_meta,
        TX_SOF_POS => open,
        TX_EOF_POS => open,
        TX_SOF     => up1_pipe_mfb_sof,
        TX_EOF     => up1_pipe_mfb_eof,
        TX_SRC_RDY => up1_pipe_mfb_src_rdy,
        TX_DST_RDY => up1_pipe_mfb_dst_rdy
    );

    up1_pipe_mfb_meta_arr <= slv_array_downto_deser(up1_pipe_mfb_meta,MFB_REGIONS,MFB_UP_META_WIDTH);

    up1_tlp_type_h_tile_g : if ENDPOINT_TYPE = "H_TILE" generate
        arr_g : for i in 0 to MFB_REGIONS-1 generate
            up1_pipe_tlp_type_arr(i) <= up1_pipe_mfb_data(i*256+31 downto i*256+24);
            up1_pipe_tlp_len_arr(i)  <= up1_pipe_mfb_data(i*256+9 downto i*256);
        end generate;
    end generate;

    up1_tlp_type_p_tile_g : if ENDPOINT_TYPE = "P_TILE" or ENDPOINT_TYPE = "R_TILE" generate
        arr_g : for i in 0 to MFB_REGIONS-1 generate
            up1_pipe_tlp_type_arr(i) <= up1_pipe_mfb_meta_arr(i)(31 downto 24);
            up1_pipe_tlp_len_arr(i)  <= up1_pipe_mfb_meta_arr(i)(9 downto 0);
        end generate;
    end generate;

    up1_pipe_tlp_vld <= up1_pipe_mfb_src_rdy and up1_pipe_mfb_sof;

    crdt_up_ptc_i : entity work.CB_RTILE_CRDT_UP
    generic map(
        REGIONS     => MFB_REGIONS,
        CRDT_ENABLE => False,
        PCIE_MPS_DW => PCIE_MPS_DW
    )
    port map(
        CLK            => CLK,
        RESET          => RESET,

        CRDT_INIT_DONE => CRDT_UP_INIT_DONE,
        CRDT_UPDATE    => CRDT_UP_UPDATE,
        CRDT_CNT_PH    => CRDT_UP_CNT_PH,
        CRDT_CNT_NPH   => CRDT_UP_CNT_NPH,
        CRDT_CNT_CPLH  => (others => '0'),
        CRDT_CNT_PD    => CRDT_UP_CNT_PD,
        CRDT_CNT_NPD   => CRDT_UP_CNT_NPD,
        CRDT_CNT_CPLD  => (others => '0'),

        TLP_FMT_TYPE   => up1_pipe_tlp_type_arr,
        TLP_LENGTH     => up1_pipe_tlp_len_arr,
        TLP_HDR_VLD    => up1_pipe_tlp_vld,
        TLP_CRDT_OK    => up1_pipe_crdt_ok,
        READY          => up1_pipe_mfb_dst_rdy_2
    );

    up1_pipe_mfb_src_rdy_2 <= up1_pipe_mfb_src_rdy and up1_pipe_crdt_ok;
    up1_pipe_mfb_dst_rdy   <= up1_pipe_mfb_dst_rdy_2 and up1_pipe_crdt_ok;

    -- MFB merger
    mfb_merger_i : entity work.MFB_MERGER_SIMPLE
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => MFB_UP_META_WIDTH,
        MASKING_EN  => False,
        CNT_MAX     => MFB_MERGER_CNT_MAX
    )
    port map(
        CLK             => CLK,
        RST             => RESET,

        RX_MFB0_DATA    => up0_pipe_mfb_data,
        RX_MFB0_META    => up0_pipe_mfb_meta,
        RX_MFB0_SOF     => up0_pipe_mfb_sof,
        RX_MFB0_EOF     => up0_pipe_mfb_eof,
        RX_MFB0_SOF_POS => (others => '0'),
        RX_MFB0_EOF_POS => (others => '0'),
        RX_MFB0_SRC_RDY => up0_pipe_mfb_src_rdy_2,
        RX_MFB0_DST_RDY => up0_pipe_mfb_dst_rdy_2,

        RX_MFB1_DATA    => up1_pipe_mfb_data,
        RX_MFB1_META    => up1_pipe_mfb_meta,
        RX_MFB1_SOF     => up1_pipe_mfb_sof,
        RX_MFB1_EOF     => up1_pipe_mfb_eof,
        RX_MFB1_SOF_POS => (others => '0'),
        RX_MFB1_EOF_POS => (others => '0'),
        RX_MFB1_SRC_RDY => up1_pipe_mfb_src_rdy_2,
        RX_MFB1_DST_RDY => up1_pipe_mfb_dst_rdy_2,

        TX_MFB_DATA     => up_mfb_data,
        TX_MFB_META     => up_mfb_meta,
        TX_MFB_SOF      => up_mfb_sof,
        TX_MFB_EOF      => up_mfb_eof,
        TX_MFB_SOF_POS  => open,
        TX_MFB_EOF_POS  => open,
        TX_MFB_SRC_RDY  => up_mfb_src_rdy,
        TX_MFB_DST_RDY  => up_mfb_dst_rdy
    );

    up_mfb_pipe_i : entity work.MFB_PIPE
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => MFB_UP_META_WIDTH,
        FAKE_PIPE   => false,
        USE_DST_RDY => true,
        PIPE_TYPE   => PIPE_TYPE,
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => up_mfb_data,
        RX_META    => up_mfb_meta,
        RX_SOF_POS => (others => '0'),
        RX_EOF_POS => (others => '0'),
        RX_SOF     => up_mfb_sof,
        RX_EOF     => up_mfb_eof,
        RX_SRC_RDY => up_mfb_src_rdy,
        RX_DST_RDY => up_mfb_dst_rdy,

        TX_DATA    => up_pipe_mfb_data,
        TX_META    => up_pipe_mfb_meta,
        TX_SOF_POS => open,
        TX_EOF_POS => open,
        TX_SOF     => up_pipe_mfb_sof,
        TX_EOF     => up_pipe_mfb_eof,
        TX_SRC_RDY => up_pipe_mfb_src_rdy,
        TX_DST_RDY => up_pipe_mfb_dst_rdy
    );

    -- conversion MFB2AVST
    mfb2avst_i : entity work.PCIE_MFB2AVST
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => MFB_UP_META_WIDTH
    )
    port map(
        CLK            => CLK,
        RST            => RESET,

        RX_MFB_DATA    => up_pipe_mfb_data,
        RX_MFB_META    => up_pipe_mfb_meta,
        RX_MFB_SOF     => up_pipe_mfb_sof,
        RX_MFB_EOF     => up_pipe_mfb_eof,
        RX_MFB_EOF_POS => (others => '0'),
        RX_MFB_SRC_RDY => up_pipe_mfb_src_rdy,
        RX_MFB_DST_RDY => up_pipe_mfb_dst_rdy,

        TX_AVST_DATA   => TX_AVST_DATA,
        TX_AVST_META   => tx_avst_meta,
        TX_AVST_SOP    => TX_AVST_SOP,
        TX_AVST_EOP    => TX_AVST_EOP,
        TX_AVST_EMPTY  => open,
        TX_AVST_VALID  => TX_AVST_VALID,
        TX_AVST_READY  => TX_AVST_READY
    );

    tx_avst_meta_arr <= slv_array_downto_deser(tx_avst_meta,MFB_REGIONS,MFB_UP_META_WIDTH);

    tx_avst_meta_unpack_g : for i in 0 to MFB_REGIONS-1 generate
        tx_avst_prefix_arr(i) <= tx_avst_meta_arr(i)(MFB_UP_META_WIDTH-1 downto 128);
        tx_avst_hdr_arr(i)(128-1 downto 96) <= tx_avst_meta_arr(i)(32-1 downto 0);
        tx_avst_hdr_arr(i)(96-1 downto 64)  <= tx_avst_meta_arr(i)(64-1 downto 32);
        tx_avst_hdr_arr(i)(64-1 downto 32)  <= tx_avst_meta_arr(i)(96-1 downto 64);
        tx_avst_hdr_arr(i)(32-1 downto 0)   <= tx_avst_meta_arr(i)(128-1 downto 96);
    end generate;

    TX_AVST_HDR    <= slv_array_ser(tx_avst_hdr_arr,MFB_REGIONS,128);
    TX_AVST_PREFIX <= slv_array_ser(tx_avst_prefix_arr,MFB_REGIONS,32);
    TX_AVST_ERROR  <= (others => '0');

    -- debug
    tx_inc_frame_g : for r in 0 to MFB_REGIONS-1 generate
        tx_inc_frame(r+1) <= (up_pipe_mfb_sof(r) and not up_pipe_mfb_eof(r) and not tx_inc_frame(r)) or
                          (up_pipe_mfb_sof(r) and up_pipe_mfb_eof(r) and tx_inc_frame(r)) or
                          (not up_pipe_mfb_sof(r) and not up_pipe_mfb_eof(r) and tx_inc_frame(r));
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                tx_inc_frame(0) <= '0';
            elsif (up_pipe_mfb_src_rdy = '1' and up_pipe_mfb_dst_rdy = '1') then
                tx_inc_frame(0) <= tx_inc_frame(MFB_REGIONS);
            end if;
        end if;
    end process;

    tx_gap_inside_frame_dbg <= tx_inc_frame(0) and not up_pipe_mfb_src_rdy;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (tx_gap_inside_frame_dbg = '1') then
                tx_gap_inside_frame_dbg_reg <= '1';
            end if;
            if (RESET = '1') then
                tx_gap_inside_frame_dbg_reg <= '0';
            end if;
        end if;
    end process;

    assert (tx_gap_inside_frame_dbg_reg /= '1')
        report "PCIE_CONNECTION_BLOCK: Gap inside frame on TX stream!"
        severity failure;

end architecture;
