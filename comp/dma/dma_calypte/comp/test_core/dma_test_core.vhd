-- dma_test_core.vhd: This is for testing the DMA Calypte
-- Copyright (C) 2023 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Note:

entity DMA_TEST_CORE is
    generic (
        DEVICE : string := "ULTRASCALE";

        MFB_REGIONS     : natural := 1;
        MFB_REGION_SIZE : natural := 8;
        MFB_BLOCK_SIZE  : natural := 8;
        MFB_ITEM_WIDTH  : natural := 8;

        HDR_META_WIDTH : natural := 24;

        RX_CHANNELS : natural := 8;
        TX_CHANNELS : natural := 8;

        USR_RX_PKT_SIZE_MAX : natural := 2**12;
        USR_TX_PKT_SIZE_MAX : natural := 2**12;

        MFB_LOOPBACK_EN    : boolean := TRUE;
        LATENCY_METER_EN   : boolean := TRUE;
        TX_DMA_DBG_CORE_EN : boolean := TRUE;
        RX_DMA_DBG_CORE_EN : boolean := TRUE;

        ST_SP_DBG_SIGNAL_W : natural := 2;
        -- Width of MI bus
        MI_WIDTH           : natural := 32
        );
    port(
        -- =======================================================================
        -- CLOCK AND RESET
        -- =======================================================================
        CLK   : in std_logic;
        RESET : in std_logic;

        -- =========================================================================================
        -- Various other debug interfaces
        -- =========================================================================================
        ST_SP_DBG_CHAN : in  std_logic_vector(log2(TX_CHANNELS) -1 downto 0);
        ST_SP_DBG_META : in  std_logic_vector(ST_SP_DBG_SIGNAL_W - 1 downto 0);
        FORCE_RESET    : out std_logic;

        -- =========================================================================================
        -- MFB interfaces
        -- =========================================================================================
        RX_MFB_DATA_IN    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_META_IN    : in  std_logic_vector(MFB_REGIONS*(log2(USR_RX_PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(RX_CHANNELS))-1 downto 0);
        RX_MFB_SOF_POS_IN : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS_IN : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF_IN     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF_IN     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SRC_RDY_IN : in  std_logic;
        RX_MFB_DST_RDY_IN : out std_logic;

        RX_MFB_META_PKT_SIZE_OUT : out std_logic_vector(log2(USR_RX_PKT_SIZE_MAX+1) -1 downto 0);
        RX_MFB_META_HDR_META_OUT : out std_logic_vector(HDR_META_WIDTH -1 downto 0);
        RX_MFB_META_CHAN_OUT     : out std_logic_vector(log2(RX_CHANNELS) -1 downto 0);

        RX_MFB_DATA_OUT    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF_POS_OUT : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS_OUT : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF_OUT     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF_OUT     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SRC_RDY_OUT : out std_logic;
        RX_MFB_DST_RDY_OUT : in  std_logic;

        TX_MFB_META_PKT_SIZE_IN : in std_logic_vector(log2(USR_TX_PKT_SIZE_MAX+1) -1 downto 0);
        TX_MFB_META_HDR_META_IN : in std_logic_vector(HDR_META_WIDTH -1 downto 0);
        TX_MFB_META_CHAN_IN     : in std_logic_vector(log2(TX_CHANNELS) -1 downto 0);

        TX_MFB_DATA_IN    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF_POS_IN : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS_IN : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SOF_IN     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF_IN     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SRC_RDY_IN : in  std_logic;
        TX_MFB_DST_RDY_IN : out std_logic;

        TX_MFB_DATA_OUT    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_META_OUT    : out std_logic_vector(MFB_REGIONS*(log2(USR_TX_PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(TX_CHANNELS))-1 downto 0);
        TX_MFB_SOF_POS_OUT : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS_OUT : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SOF_OUT     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF_OUT     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SRC_RDY_OUT : out std_logic;
        TX_MFB_DST_RDY_OUT : in  std_logic;

        -- =====================================================================
        -- MI interface for SW access
        -- =====================================================================
        MI_CLK   : in std_logic;
        MI_RESET : in std_logic;

        MI_ADDR : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_DWR  : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_BE   : in  std_logic_vector(MI_WIDTH/8-1 downto 0);
        MI_RD   : in  std_logic;
        MI_WR   : in  std_logic;
        MI_DRD  : out std_logic_vector(MI_WIDTH-1 downto 0);
        MI_ARDY : out std_logic;
        MI_DRDY : out std_logic
        );
end entity;

architecture FULL of DMA_TEST_CORE is

    constant MI_SPLIT_PORTS : natural := 5;
    constant MI_SPLIT_BASES : slv_array_t(MI_SPLIT_PORTS-1 downto 0)(MI_WIDTH-1 downto 0) := (
        0 => X"00000000",               -- MFB Loopback
        1 => X"00010000",               -- TX DMA Debug Core
        2 => X"00020000",               -- Latency meter
        3 => X"00030000",               -- Reset FSM
        4 => X"00040000"                -- RX DMA Debug Core
        );
    constant MI_SPLIT_ADDR_MASK : std_logic_vector(MI_WIDTH -1 downto 0) := X"00070000";

    -- MI Asynchronous crossing
    signal mi_dwr_sync  : std_logic_vector(MI_WIDTH -1 downto 0);
    signal mi_addr_sync : std_logic_vector(MI_WIDTH -1 downto 0);
    signal mi_be_sync   : std_logic_vector(MI_WIDTH/8 -1 downto 0);
    signal mi_rd_sync   : std_logic;
    signal mi_wr_sync   : std_logic;
    signal mi_drd_sync  : std_logic_vector(MI_WIDTH-1 downto 0);
    signal mi_ardy_sync : std_logic;
    signal mi_drdy_sync : std_logic;

    -- MI Splitter outputs
    signal mi_dwr_split  : slv_array_t(MI_SPLIT_PORTS-1 downto 0)(MI_WIDTH -1 downto 0);
    signal mi_addr_split : slv_array_t(MI_SPLIT_PORTS-1 downto 0)(MI_WIDTH -1 downto 0);
    signal mi_be_split   : slv_array_t(MI_SPLIT_PORTS-1 downto 0)(MI_WIDTH/8 -1 downto 0);
    signal mi_rd_split   : std_logic_vector(MI_SPLIT_PORTS-1 downto 0);
    signal mi_wr_split   : std_logic_vector(MI_SPLIT_PORTS-1 downto 0);
    signal mi_drd_split  : slv_array_t(MI_SPLIT_PORTS-1 downto 0)(MI_WIDTH -1 downto 0);
    signal mi_ardy_split : std_logic_vector(MI_SPLIT_PORTS-1 downto 0);
    signal mi_drdy_split : std_logic_vector(MI_SPLIT_PORTS-1 downto 0);

    -- =============================================================================================
    -- TX Debug Core ---> MFB Loopback
    -- =============================================================================================
    signal tx_mfb_data_dbg    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH -1 downto 0);
    signal tx_mfb_meta_dbg    : std_logic_vector(log2(USR_TX_PKT_SIZE_MAX +1)+HDR_META_WIDTH+log2(TX_CHANNELS) -1 downto 0);
    signal tx_mfb_sof_dbg     : std_logic_vector(MFB_REGIONS -1 downto 0);
    signal tx_mfb_eof_dbg     : std_logic_vector(MFB_REGIONS -1 downto 0);
    signal tx_mfb_sof_pos_dbg : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)) -1 downto 0);
    signal tx_mfb_eof_pos_dbg : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
    signal tx_mfb_src_rdy_dbg : std_logic;
    signal tx_mfb_dst_rdy_dbg : std_logic;

    -- =============================================================================================
    -- MFB Generator ----> MUX
    -- =============================================================================================
    signal rx_mfb_data_gen    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH -1 downto 0);
    signal rx_mfb_meta_gen    : std_logic_vector(log2(RX_CHANNELS) + log2(USR_RX_PKT_SIZE_MAX +1) -1 downto 0);
    signal rx_mfb_sof_gen     : std_logic_vector(MFB_REGIONS -1 downto 0);
    signal rx_mfb_eof_gen     : std_logic_vector(MFB_REGIONS -1 downto 0);
    signal rx_mfb_sof_pos_gen : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)) -1 downto 0);
    signal rx_mfb_eof_pos_gen : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
    signal rx_mfb_src_rdy_gen : std_logic;
    signal rx_mfb_dst_rdy_gen : std_logic;

    -- =============================================================================================
    -- MFB Loopback ----> MUX
    -- =============================================================================================
    signal rx_mfb_data_lbk    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH -1 downto 0);
    signal rx_mfb_meta_lbk    : std_logic_vector(log2(RX_CHANNELS) + log2(USR_RX_PKT_SIZE_MAX +1) + HDR_META_WIDTH -1 downto 0);
    signal rx_mfb_sof_lbk     : std_logic_vector(MFB_REGIONS -1 downto 0);
    signal rx_mfb_eof_lbk     : std_logic_vector(MFB_REGIONS -1 downto 0);
    signal rx_mfb_sof_pos_lbk : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)) -1 downto 0);
    signal rx_mfb_eof_pos_lbk : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
    signal rx_mfb_src_rdy_lbk : std_logic;
    signal rx_mfb_dst_rdy_lbk : std_logic;

    -- =============================================================================================
    -- MFB generator control
    -- =============================================================================================
    signal mfb_gen_ctrl_en          : std_logic;
    signal mfb_gen_ctrl_chan_inc    : std_logic_vector(32-1 downto 0);
    signal mfb_gen_ctrl_chan_val    : std_logic_vector(32-1 downto 0);
    signal mfb_gen_ctrl_length      : std_logic_vector(log2(USR_RX_PKT_SIZE_MAX+1) -1 downto 0);
    signal mfb_gen_ctrl_pkt_cnt_clr : std_logic;
    signal mfb_gen_ctrl_pkt_cnt     : std_logic_vector(64 -1 downto 0);

    -- =============================================================================================
    -- RX MFB Generator/RX stream multiplexer ---> RX Debug Core
    -- =============================================================================================
    signal rx_mfb_meta_pkt_size_gen_mux : std_logic_vector(log2(USR_RX_PKT_SIZE_MAX+1) -1 downto 0);
    signal rx_mfb_meta_hdr_meta_gen_mux : std_logic_vector(HDR_META_WIDTH -1 downto 0);
    signal rx_mfb_meta_chan_gen_mux     : std_logic_vector(log2(RX_CHANNELS) -1 downto 0);

    signal rx_mfb_data_gen_mux    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH -1 downto 0);
    signal rx_mfb_meta_gen_mux    : std_logic_vector(log2(RX_CHANNELS) + log2(USR_RX_PKT_SIZE_MAX +1) + HDR_META_WIDTH -1 downto 0);
    signal rx_mfb_sof_gen_mux     : std_logic_vector(MFB_REGIONS -1 downto 0);
    signal rx_mfb_eof_gen_mux     : std_logic_vector(MFB_REGIONS -1 downto 0);
    signal rx_mfb_sof_pos_gen_mux : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)) -1 downto 0);
    signal rx_mfb_eof_pos_gen_mux : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
    signal rx_mfb_src_rdy_gen_mux : std_logic;
    signal rx_mfb_dst_rdy_gen_mux : std_logic;

    -- =============================================================================================
    -- Lanecy meters
    -- =============================================================================================
    constant TIMESTAMP_WIDTH  : positive := 11;
    constant LAT_PARAL_EVENTS : positive := 64;

    signal lat_meas_val_vld    : std_logic;
    signal lat_meas_val        : std_logic_vector(TIMESTAMP_WIDTH -1 downto 0);
    signal lat_meas_fifo_full  : std_logic;
    signal lat_meas_fifo_items : std_logic_vector(log2(LAT_PARAL_EVENTS) downto 0);

    type meas_fsm_state_t is (S_IDLE, S_COUNT_TESTING_PACKETS, S_TEST_FINISHED);
    signal meas_fsm_pst : meas_fsm_state_t := S_IDLE;
    signal meas_fsm_nst : meas_fsm_state_t := S_IDLE;
    signal pkt_cnt_pst : unsigned(15 downto 0);
    signal pkt_cnt_nst : unsigned(15 downto 0);
    signal test_finished : std_logic;

    -- =============================================================================================
    -- Reset FSM
    -- =============================================================================================
    signal rst_fsm_trigg : std_logic;
    type rst_fsm_state_t is (IDLE, RESET_COUNTING);
    signal rst_pst  : rst_fsm_state_t := IDLE;
    signal rst_nst  : rst_fsm_state_t := IDLE;
    signal rst_cntr_pst : unsigned(9 downto 0);
    signal rst_cntr_nst : unsigned(9 downto 0);

    -- =============================================================================================
    -- Miscelaneous
    -- =============================================================================================
    signal tst_gen_mux_sel   : std_logic;
    signal data_logger_rst   : std_logic;
    signal data_logger_ctrlo : std_logic_vector((1+1+log2(USR_RX_PKT_SIZE_MAX+1)+32+32+1) -1 downto 0);
    signal rx_mfb_meta_dbg   : std_logic_vector(log2(USR_RX_PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(RX_CHANNELS) -1 downto 0);

    -- =============================================================================================
    -- Debug probes
    -- =============================================================================================
    attribute mark_debug : string;

    attribute mark_debug of data_logger_rst : signal is "true";
    attribute mark_debug of tst_gen_mux_sel : signal is "true";
    attribute mark_debug of meas_fsm_pst    : signal is "true";
    attribute mark_debug of pkt_cnt_pst     : signal is "true";
    attribute mark_debug of test_finished   : signal is "true";

    attribute mark_debug of mfb_gen_ctrl_pkt_cnt_clr : signal is "true";
    attribute mark_debug of mfb_gen_ctrl_length      : signal is "true";
    attribute mark_debug of mfb_gen_ctrl_chan_val    : signal is "true";
    attribute mark_debug of mfb_gen_ctrl_chan_inc    : signal is "true";
    attribute mark_debug of mfb_gen_ctrl_en          : signal is "true";
    attribute mark_debug of mfb_gen_ctrl_pkt_cnt     : signal is "true";

    attribute mark_debug of lat_meas_val        : signal is "true";
    attribute mark_debug of lat_meas_val_vld    : signal is "true";
    attribute mark_debug of lat_meas_fifo_full  : signal is "true";
    attribute mark_debug of lat_meas_fifo_items : signal is "true";
begin
    mi_async_i : entity work.MI_ASYNC
        generic map(
            ADDR_WIDTH => MI_WIDTH,
            DATA_WIDTH => MI_WIDTH,
            DEVICE     => DEVICE
            )
        port map(
            CLK_M   => MI_CLK,
            RESET_M => MI_RESET,

            MI_M_ADDR => MI_ADDR,
            MI_M_DWR  => MI_DWR,
            MI_M_BE   => MI_BE,
            MI_M_RD   => MI_RD,
            MI_M_WR   => MI_WR,
            MI_M_ARDY => MI_ARDY,
            MI_M_DRDY => MI_DRDY,
            MI_M_DRD  => MI_DRD,

            CLK_S   => CLK,
            RESET_S => RESET,

            MI_S_ADDR => mi_addr_sync,
            MI_S_DWR  => mi_dwr_sync,
            MI_S_BE   => mi_be_sync,
            MI_S_RD   => mi_rd_sync,
            MI_S_WR   => mi_wr_sync,
            MI_S_ARDY => mi_ardy_sync,
            MI_S_DRDY => mi_drdy_sync,
            MI_S_DRD  => mi_drd_sync);

    mi_gen_spl_i : entity work.MI_SPLITTER_PLUS_GEN
        generic map(
            ADDR_WIDTH => MI_WIDTH,
            DATA_WIDTH => MI_WIDTH,
            META_WIDTH => 0,
            PORTS      => MI_SPLIT_PORTS,
            PIPE_OUT   => (others => FALSE),

            ADDR_MASK  => MI_SPLIT_ADDR_MASK,
            ADDR_BASES => MI_SPLIT_PORTS,
            ADDR_BASE  => MI_SPLIT_BASES,

            DEVICE => DEVICE
            )
        port map(
            CLK   => CLK,
            RESET => RESET,

            RX_DWR  => mi_dwr_sync,
            RX_MWR  => (others => '0'),
            RX_ADDR => mi_addr_sync,
            RX_BE   => mi_be_sync,
            RX_RD   => mi_rd_sync,
            RX_WR   => mi_wr_sync,
            RX_ARDY => mi_ardy_sync,
            RX_DRD  => mi_drd_sync,
            RX_DRDY => mi_drdy_sync,

            TX_DWR  => mi_dwr_split,
            TX_MWR  => open,
            TX_ADDR => mi_addr_split,
            TX_BE   => mi_be_split,
            TX_RD   => mi_rd_split,
            TX_WR   => mi_wr_split,
            TX_ARDY => mi_ardy_split,
            TX_DRD  => mi_drd_split,
            TX_DRDY => mi_drdy_split);

    tx_dma_debug_core_g: if (TX_DMA_DBG_CORE_EN) generate
        tx_debug_core_i : entity work.TX_DMA_DEBUG_CORE
            generic map (
                DEVICE             => DEVICE,

                MFB_REGIONS        => MFB_REGIONS,
                MFB_REGION_SIZE    => MFB_REGION_SIZE,
                MFB_BLOCK_SIZE     => MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH     => MFB_ITEM_WIDTH,

                DMA_META_WIDTH     => HDR_META_WIDTH,
                PKT_SIZE_MAX       => USR_TX_PKT_SIZE_MAX,
                CHANNELS           => TX_CHANNELS,

                DBG_CNTRS_WIDTH    => 64,
                ST_SP_DBG_SIGNAL_W => ST_SP_DBG_SIGNAL_W,
                MI_WIDTH           => MI_WIDTH,
                MI_SAME_CLK        => TRUE)
            port map (
                CLK                  => CLK,
                RESET                => RESET,

                ST_SP_DBG_CHAN       => ST_SP_DBG_CHAN,
                ST_SP_DBG_META       => ST_SP_DBG_META,

                RX_MFB_META_PKT_SIZE => TX_MFB_META_PKT_SIZE_IN,
                RX_MFB_META_CHAN     => TX_MFB_META_CHAN_IN,
                RX_MFB_META_HDR_META => TX_MFB_META_HDR_META_IN,

                RX_MFB_DATA          => TX_MFB_DATA_IN,
                RX_MFB_SOF_POS       => TX_MFB_SOF_POS_IN,
                RX_MFB_EOF_POS       => TX_MFB_EOF_POS_IN,
                RX_MFB_SOF           => TX_MFB_SOF_IN,
                RX_MFB_EOF           => TX_MFB_EOF_IN,
                RX_MFB_SRC_RDY       => TX_MFB_SRC_RDY_IN,
                RX_MFB_DST_RDY       => TX_MFB_DST_RDY_IN,

                TX_MFB_DATA          => tx_mfb_data_dbg,
                TX_MFB_META          => tx_mfb_meta_dbg,
                TX_MFB_SOF_POS       => tx_mfb_sof_pos_dbg,
                TX_MFB_EOF_POS       => tx_mfb_eof_pos_dbg,
                TX_MFB_SOF           => tx_mfb_sof_dbg,
                TX_MFB_EOF           => tx_mfb_eof_dbg,
                TX_MFB_SRC_RDY       => tx_mfb_src_rdy_dbg,
                TX_MFB_DST_RDY       => tx_mfb_dst_rdy_dbg,

                MI_CLK               => MI_CLK,
                MI_RESET             => MI_RESET,

                MI_ADDR              => mi_addr_split(1),
                MI_DWR               => mi_dwr_split(1),
                MI_BE                => mi_be_split(1),
                MI_RD                => mi_rd_split(1),
                MI_WR                => mi_wr_split(1),
                MI_DRD               => mi_drd_split(1),
                MI_ARDY              => mi_ardy_split(1),
                MI_DRDY              => mi_drdy_split(1)
                );
    else generate
        mi_drd_split(1)  <= X"DEADBEAD";
        mi_ardy_split(1) <= mi_rd_split(1) or mi_wr_split(1);
        mi_drdy_split(1) <= mi_rd_split(1);

        tx_mfb_data_dbg    <= TX_MFB_DATA_IN;
        tx_mfb_meta_dbg    <= TX_MFB_META_PKT_SIZE_IN & TX_MFB_META_HDR_META_IN & TX_MFB_META_CHAN_IN;
        tx_mfb_sof_dbg     <= TX_MFB_SOF_IN;
        tx_mfb_eof_dbg     <= TX_MFB_EOF_IN;
        tx_mfb_sof_pos_dbg <= TX_MFB_SOF_POS_IN;
        tx_mfb_eof_pos_dbg <= TX_MFB_EOF_POS_IN;
        tx_mfb_src_rdy_dbg <= TX_MFB_SRC_RDY_IN;
        TX_MFB_DST_RDY_IN  <= tx_mfb_dst_rdy_dbg;
    end generate;

    mfb_loopback_i : entity work.MFB_LOOPBACK
        generic map (
            REGIONS     => MFB_REGIONS,
            REGION_SIZE => MFB_REGION_SIZE,
            BLOCK_SIZE  => MFB_BLOCK_SIZE,
            ITEM_WIDTH  => MFB_ITEM_WIDTH,
            META_WIDTH  => log2(maximum(TX_CHANNELS, RX_CHANNELS)) + log2(maximum(USR_RX_PKT_SIZE_MAX, USR_TX_PKT_SIZE_MAX)+1) + HDR_META_WIDTH,

            FAKE_LOOPBACK => (not MFB_LOOPBACK_EN),
            PIPED_PORTS   => TRUE,
            SAME_CLK      => TRUE)
        port map (
            MI_CLK   => MI_CLK,
            MI_RESET => MI_RESET,

            MI_DWR  => mi_dwr_split(0),
            MI_ADDR => mi_addr_split(0),
            MI_RD   => mi_rd_split(0),
            MI_WR   => mi_wr_split(0),
            MI_ARDY => mi_ardy_split(0),
            MI_DRD  => mi_drd_split(0),
            MI_DRDY => mi_drdy_split(0),

            CLK   => CLK,
            RESET => RESET,

            RX_DATA_IN    => RX_MFB_DATA_IN,
            RX_META_IN    => RX_MFB_META_IN,
            RX_SOF_IN     => RX_MFB_SOF_IN,
            RX_EOF_IN     => RX_MFB_EOF_IN,
            RX_SOF_POS_IN => RX_MFB_SOF_POS_IN,
            RX_EOF_POS_IN => RX_MFB_EOF_POS_IN,
            RX_SRC_RDY_IN => RX_MFB_SRC_RDY_IN,
            RX_DST_RDY_IN => RX_MFB_DST_RDY_IN,

            RX_DATA_OUT    => rx_mfb_data_lbk,
            RX_META_OUT    => rx_mfb_meta_lbk,
            RX_SOF_OUT     => rx_mfb_sof_lbk,
            RX_EOF_OUT     => rx_mfb_eof_lbk,
            RX_SOF_POS_OUT => rx_mfb_sof_pos_lbk,
            RX_EOF_POS_OUT => rx_mfb_eof_pos_lbk,
            RX_SRC_RDY_OUT => rx_mfb_src_rdy_lbk,
            RX_DST_RDY_OUT => rx_mfb_dst_rdy_lbk,

            TX_DATA_OUT    => TX_MFB_DATA_OUT,
            TX_META_OUT    => TX_MFB_META_OUT,
            TX_SOF_OUT     => TX_MFB_SOF_OUT,
            TX_EOF_OUT     => TX_MFB_EOF_OUT,
            TX_SOF_POS_OUT => TX_MFB_SOF_POS_OUT,
            TX_EOF_POS_OUT => TX_MFB_EOF_POS_OUT,
            TX_SRC_RDY_OUT => TX_MFB_SRC_RDY_OUT,
            TX_DST_RDY_OUT => TX_MFB_DST_RDY_OUT,

            TX_DATA_IN    => tx_mfb_data_dbg,
            TX_META_IN    => tx_mfb_meta_dbg,
            TX_SOF_IN     => tx_mfb_sof_dbg,
            TX_EOF_IN     => tx_mfb_eof_dbg,
            TX_SOF_POS_IN => tx_mfb_sof_pos_dbg,
            TX_EOF_POS_IN => tx_mfb_eof_pos_dbg,
            TX_SRC_RDY_IN => tx_mfb_src_rdy_dbg,
            TX_DST_RDY_IN => tx_mfb_dst_rdy_dbg);

    -- =============================================================================================
    -- Latency measurement
    -- =============================================================================================
    (tst_gen_mux_sel,
     mfb_gen_ctrl_pkt_cnt_clr,
     mfb_gen_ctrl_en,
     mfb_gen_ctrl_length,
     mfb_gen_ctrl_chan_val,
     mfb_gen_ctrl_chan_inc)
        <= data_logger_ctrlo;

    latency_meter_g: if (LATENCY_METER_EN) generate
        data_logger_i: entity work.DATA_LOGGER
            generic map (
                MI_DATA_WIDTH   => MI_WIDTH,
                MI_ADDR_WIDTH   => MI_WIDTH,

                CNTER_CNT       => 0,
                VALUE_CNT       => 1,

                -- MUX for MFB Generator + all signals to control the generator
                CTRLO_WIDTH     => data_logger_ctrlo'length,
                -- Counter
                CTRLI_WIDTH     => 1+64+log2(LAT_PARAL_EVENTS)+1+1,

                CNTER_WIDTH     => 64,
                VALUE_WIDTH     => (others => TIMESTAMP_WIDTH),

                MIN_EN          => (others => true),
                MAX_EN          => (others => true),
                SUM_EN          => (others => false),
                HIST_EN         => (others => true),

                SUM_EXTRA_WIDTH => (others => 16),
                HIST_BOX_CNT    => (others => 100),
                HIST_BOX_WIDTH  => (others => 32),
                CTRLO_DEFAULT   => (others => '0'))
            port map (
                CLK           => CLK,
                RST           => RESET,

                RST_DONE      => open,
                SW_RST        => data_logger_rst,

                CTRLO         => data_logger_ctrlo,
                CTRLI         => (
                    test_finished &
                    mfb_gen_ctrl_pkt_cnt &
                    lat_meas_fifo_items &
                    lat_meas_fifo_full),

                CNTERS_INCR   => (others => '0'),
                CNTERS_SUBMIT => (others => '0'),
                CNTERS_DIFF   => (others => (others => '0')),

                VALUES_VLD    => (others => lat_meas_val_vld),
                VALUES        => lat_meas_val,

                MI_DWR        => mi_dwr_split(2),
                MI_ADDR       => mi_addr_split(2),
                MI_BE         => mi_be_split(2),
                MI_RD         => mi_rd_split(2),
                MI_WR         => mi_wr_split(2),
                MI_ARDY       => mi_ardy_split(2),
                MI_DRD        => mi_drd_split(2),
                MI_DRDY       => mi_drdy_split(2));

        latency_meter_i : entity work.LATENCY_METER
            generic map (
                DATA_WIDTH         => TIMESTAMP_WIDTH,
                MAX_PARALEL_EVENTS => LAT_PARAL_EVENTS,
                DEVICE             => DEVICE)
            port map (
                CLK         => CLK,
                RST         => RESET or data_logger_rst,

                START_EVENT => RX_MFB_SOF_OUT(0) and RX_MFB_SRC_RDY_OUT and RX_MFB_DST_RDY_OUT,
                END_EVENT   => TX_MFB_SOF_IN(0)  and TX_MFB_SRC_RDY_IN  and TX_MFB_DST_RDY_IN,

                LATENCY_VLD => lat_meas_val_vld,
                LATENCY     => lat_meas_val,

                FIFO_FULL   => lat_meas_fifo_full,
                FIFO_ITEMS  => lat_meas_fifo_items);

        meas_director_fsm_reg_p : process (CLK) is
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1' or data_logger_rst = '1') then
                    meas_fsm_pst <= S_IDLE;
                    pkt_cnt_pst  <= (others => '0');
                else
                    meas_fsm_pst <= meas_fsm_nst;
                    pkt_cnt_pst  <= pkt_cnt_nst;
                end if;
            end if;
        end process;

        meas_director_fsm_nst_logic_p : process (all) is
            variable bst_init_count : unsigned(15 downto 0);
            variable bst_mode_en    : std_logic;
        begin
            meas_fsm_nst <= meas_fsm_pst;
            pkt_cnt_nst  <= pkt_cnt_pst;

            test_finished <= '0';

            bst_init_count := unsigned(mfb_gen_ctrl_chan_inc(31 downto 16));
            bst_mode_en    := mfb_gen_ctrl_chan_inc(9);

            case meas_fsm_pst is
                when S_IDLE =>

                    -- Enable testing check only when burst mode in the generator is enabled
                    if (mfb_gen_ctrl_en = '1'
                        and bst_mode_en = '1'
                        and RX_MFB_SRC_RDY_OUT = '1'
                        and RX_MFB_DST_RDY_OUT = '1') then

                        meas_fsm_nst <= S_COUNT_TESTING_PACKETS;
                        pkt_cnt_nst  <= bst_init_count - 1;
                    end if;

                when S_COUNT_TESTING_PACKETS =>

                    if (
                        RX_MFB_SRC_RDY_OUT = '1'
                        and RX_MFB_DST_RDY_OUT = '1'
                        and pkt_cnt_pst > 0) then

                        pkt_cnt_nst <= pkt_cnt_pst -1;
                    end if;

                    if (pkt_cnt_pst = 0 and unsigned(lat_meas_fifo_items) = 0) then
                        meas_fsm_nst <= S_TEST_FINISHED;
                    end if;

                when S_TEST_FINISHED =>

                    test_finished <= '1';

                    if (mfb_gen_ctrl_en = '0') then
                        meas_fsm_nst <= S_IDLE;
                    end if;

            end case;
        end process;

        mfb_generator_i: entity work.MFB_GENERATOR
            generic map (
                REGIONS        => MFB_REGIONS,
                REGION_SIZE    => MFB_REGION_SIZE,
                BLOCK_SIZE     => MFB_BLOCK_SIZE,
                ITEM_WIDTH     => MFB_ITEM_WIDTH,

                LENGTH_WIDTH   => log2(USR_RX_PKT_SIZE_MAX+1),
                CHANNELS_WIDTH => log2(RX_CHANNELS),

                PKT_CNT_WIDTH  => 64,
                USE_PACP_ARCH  => false,
                DEVICE         => DEVICE)
            port map (
                CLK              => CLK,
                RST              => RESET or data_logger_rst,

                CTRL_EN          => mfb_gen_ctrl_en,
                CTRL_CHAN_INC    => mfb_gen_ctrl_chan_inc,
                CTRL_CHAN_VAL    => mfb_gen_ctrl_chan_val,
                CTRL_LENGTH      => mfb_gen_ctrl_length,
                CTRL_MAC_DST     => (others => '0'),
                CTRL_MAC_SRC     => (others => '0'),
                CTRL_PKT_CNT_CLR => mfb_gen_ctrl_pkt_cnt_clr,
                CTRL_PKT_CNT     => mfb_gen_ctrl_pkt_cnt,

                TX_MFB_DATA      => rx_mfb_data_gen,
                TX_MFB_META      => rx_mfb_meta_gen,
                TX_MFB_SOF       => rx_mfb_sof_gen,
                TX_MFB_EOF       => rx_mfb_eof_gen,
                TX_MFB_SOF_POS   => rx_mfb_sof_pos_gen,
                TX_MFB_EOF_POS   => rx_mfb_eof_pos_gen,
                TX_MFB_SRC_RDY   => rx_mfb_src_rdy_gen,
                TX_MFB_DST_RDY   => rx_mfb_dst_rdy_gen);

        rx_mfb_meta_pkt_size_gen_mux <= rx_mfb_meta_lbk(log2(USR_RX_PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(RX_CHANNELS) -1 downto HDR_META_WIDTH + log2(RX_CHANNELS))
                                    when tst_gen_mux_sel = '0' else rx_mfb_meta_gen(log2(USR_RX_PKT_SIZE_MAX+1) -1 downto 0);
        rx_mfb_meta_hdr_meta_gen_mux <= rx_mfb_meta_lbk(HDR_META_WIDTH + log2(RX_CHANNELS) -1 downto log2(RX_CHANNELS))
                                    when tst_gen_mux_sel = '0' else (others => '0');
        rx_mfb_meta_chan_gen_mux     <= rx_mfb_meta_lbk(log2(RX_CHANNELS) -1 downto 0)
                                    when tst_gen_mux_sel = '0' else rx_mfb_meta_gen(log2(RX_CHANNELS) + log2(USR_RX_PKT_SIZE_MAX+1) -1 downto log2(USR_RX_PKT_SIZE_MAX+1));

        rx_mfb_data_gen_mux    <= rx_mfb_data_lbk    when tst_gen_mux_sel = '0' else rx_mfb_data_gen;
        rx_mfb_sof_gen_mux     <= rx_mfb_sof_lbk     when tst_gen_mux_sel = '0' else rx_mfb_sof_gen;
        rx_mfb_eof_gen_mux     <= rx_mfb_eof_lbk     when tst_gen_mux_sel = '0' else rx_mfb_eof_gen;
        rx_mfb_sof_pos_gen_mux <= rx_mfb_sof_pos_lbk when tst_gen_mux_sel = '0' else rx_mfb_sof_pos_gen;
        rx_mfb_eof_pos_gen_mux <= rx_mfb_eof_pos_lbk when tst_gen_mux_sel = '0' else rx_mfb_eof_pos_gen;
        rx_mfb_src_rdy_gen_mux <= rx_mfb_src_rdy_lbk when tst_gen_mux_sel = '0' else rx_mfb_src_rdy_gen;

        rx_mfb_dst_rdy_lbk <= rx_mfb_dst_rdy_gen_mux when tst_gen_mux_sel = '0' else '1';
        rx_mfb_dst_rdy_gen <= rx_mfb_dst_rdy_gen_mux when tst_gen_mux_sel = '1' else '1';

    else generate
        mi_drd_split(2)  <= X"DEAD_BEAD";
        mi_ardy_split(2) <= mi_rd_split(2) or mi_wr_split(2);
        mi_drdy_split(2) <= mi_rd_split(2);

        rx_mfb_meta_pkt_size_gen_mux <= rx_mfb_meta_lbk(log2(USR_RX_PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(RX_CHANNELS) -1 downto HDR_META_WIDTH + log2(RX_CHANNELS));
        rx_mfb_meta_hdr_meta_gen_mux <= rx_mfb_meta_lbk(HDR_META_WIDTH + log2(RX_CHANNELS) -1 downto log2(RX_CHANNELS));
        rx_mfb_meta_chan_gen_mux     <= rx_mfb_meta_lbk(log2(RX_CHANNELS) -1 downto 0);

        rx_mfb_data_gen_mux    <= rx_mfb_data_lbk;
        rx_mfb_sof_gen_mux     <= rx_mfb_sof_lbk;
        rx_mfb_eof_gen_mux     <= rx_mfb_eof_lbk;
        rx_mfb_sof_pos_gen_mux <= rx_mfb_sof_pos_lbk;
        rx_mfb_eof_pos_gen_mux <= rx_mfb_eof_pos_lbk;
        rx_mfb_src_rdy_gen_mux <= rx_mfb_src_rdy_lbk;
        rx_mfb_dst_rdy_lbk     <= rx_mfb_dst_rdy_gen_mux;
    end generate;

    rx_dma_debug_core_g: if (RX_DMA_DBG_CORE_EN) generate
        rx_debug_core_i : entity work.TX_DMA_DEBUG_CORE
            generic map (
                DEVICE             => DEVICE,

                MFB_REGIONS        => MFB_REGIONS,
                MFB_REGION_SIZE    => MFB_REGION_SIZE,
                MFB_BLOCK_SIZE     => MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH     => MFB_ITEM_WIDTH,

                DMA_META_WIDTH     => HDR_META_WIDTH,
                PKT_SIZE_MAX       => USR_RX_PKT_SIZE_MAX,
                CHANNELS           => RX_CHANNELS,

                DBG_CNTRS_WIDTH    => 64,
                ST_SP_DBG_SIGNAL_W => ST_SP_DBG_SIGNAL_W,
                MI_WIDTH           => MI_WIDTH,
                MI_SAME_CLK        => TRUE)
            port map (
                CLK                  => CLK,
                RESET                => RESET,

                ST_SP_DBG_CHAN       => (others => '0'),
                ST_SP_DBG_META       => (others => '0'),

                RX_MFB_META_PKT_SIZE => rx_mfb_meta_pkt_size_gen_mux,
                RX_MFB_META_HDR_META => rx_mfb_meta_hdr_meta_gen_mux,
                RX_MFB_META_CHAN     => rx_mfb_meta_chan_gen_mux,

                RX_MFB_DATA          => rx_mfb_data_gen_mux,
                RX_MFB_SOF_POS       => rx_mfb_sof_pos_gen_mux,
                RX_MFB_EOF_POS       => rx_mfb_eof_pos_gen_mux,
                RX_MFB_SOF           => rx_mfb_sof_gen_mux,
                RX_MFB_EOF           => rx_mfb_eof_gen_mux,
                RX_MFB_SRC_RDY       => rx_mfb_src_rdy_gen_mux,
                RX_MFB_DST_RDY       => rx_mfb_dst_rdy_gen_mux,

                TX_MFB_DATA          => RX_MFB_DATA_OUT,
                TX_MFB_META          => rx_mfb_meta_dbg,
                TX_MFB_SOF_POS       => RX_MFB_SOF_POS_OUT,
                TX_MFB_EOF_POS       => RX_MFB_EOF_POS_OUT,
                TX_MFB_SOF           => RX_MFB_SOF_OUT,
                TX_MFB_EOF           => RX_MFB_EOF_OUT,
                TX_MFB_SRC_RDY       => RX_MFB_SRC_RDY_OUT,
                TX_MFB_DST_RDY       => RX_MFB_DST_RDY_OUT,

                MI_CLK               => MI_CLK,
                MI_RESET             => MI_RESET,

                MI_ADDR              => mi_addr_split(4),
                MI_DWR               => mi_dwr_split(4),
                MI_BE                => mi_be_split(4),
                MI_RD                => mi_rd_split(4),
                MI_WR                => mi_wr_split(4),
                MI_DRD               => mi_drd_split(4),
                MI_ARDY              => mi_ardy_split(4),
                MI_DRDY              => mi_drdy_split(4)
                );

        RX_MFB_META_PKT_SIZE_OUT <= rx_mfb_meta_dbg(log2(USR_RX_PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(RX_CHANNELS) -1 downto HDR_META_WIDTH + log2(RX_CHANNELS));
        RX_MFB_META_HDR_META_OUT <= rx_mfb_meta_dbg(HDR_META_WIDTH + log2(RX_CHANNELS) -1 downto log2(RX_CHANNELS));
        RX_MFB_META_CHAN_OUT     <= rx_mfb_meta_dbg(log2(RX_CHANNELS) -1 downto 0);
    else generate
        mi_drd_split(4)  <= X"DEADBEAD";
        mi_ardy_split(4) <= mi_rd_split(4) or mi_wr_split(4);
        mi_drdy_split(4) <= mi_rd_split(4);

        RX_MFB_META_PKT_SIZE_OUT <= rx_mfb_meta_pkt_size_gen_mux;
        RX_MFB_META_HDR_META_OUT <= rx_mfb_meta_hdr_meta_gen_mux;
        RX_MFB_META_CHAN_OUT     <= rx_mfb_meta_chan_gen_mux;

        RX_MFB_DATA_OUT        <= rx_mfb_data_gen_mux;
        RX_MFB_SOF_OUT         <= rx_mfb_sof_gen_mux;
        RX_MFB_EOF_OUT         <= rx_mfb_eof_gen_mux;
        RX_MFB_SOF_POS_OUT     <= rx_mfb_sof_pos_gen_mux;
        RX_MFB_EOF_POS_OUT     <= rx_mfb_eof_pos_gen_mux;
        RX_MFB_SRC_RDY_OUT     <= rx_mfb_src_rdy_gen_mux;
        rx_mfb_dst_rdy_gen_mux <= RX_MFB_DST_RDY_OUT;
    end generate;

    -- =============================================================================================
    -- Resetting FSM
    -- =============================================================================================
    mi_drd_split(3)  <= X"CAFE_BABE";
    mi_ardy_split(3) <= mi_rd_split(3) or mi_wr_split(3);
    mi_drdy_split(3) <= mi_rd_split(3);

    rst_fsm_trigg <= '1' when (mi_wr_split(3) = '1' and mi_addr_split(3)(1 downto 0) = std_logic_vector(to_unsigned(16#00#,2)) and unsigned(mi_dwr_split(3)) = 1) else '0';

    reset_fsm_state_reg : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                rst_pst      <= IDLE;
                rst_cntr_pst <= (others => '0');
            else
                rst_pst      <= rst_nst;
                rst_cntr_pst <= rst_cntr_nst;
            end if;
        end if;
    end process;

    reset_fsm_nst_logic : process (all) is
    begin
        rst_nst      <= rst_pst;
        rst_cntr_nst <= rst_cntr_pst;

        FORCE_RESET <= '0';

        case rst_pst is
            when IDLE =>

                if (rst_fsm_trigg = '1') then
                    rst_nst <= RESET_COUNTING;
                end if;

            when RESET_COUNTING =>
                FORCE_RESET  <= '1';
                rst_cntr_nst <= rst_cntr_pst + 1;

                if (rst_cntr_pst = 1023) then
                    rst_nst <= IDLE;
                end if;
        end case;
    end process;
end architecture;
