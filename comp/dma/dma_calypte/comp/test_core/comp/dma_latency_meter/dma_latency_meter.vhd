-- dma_latency_meter.vhd: latency meter for DMA controllers
-- Copyright (C) 2025 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Note:

entity DMA_LATENCY_METER is
    generic (
        DEVICE : string := "ULTRASCALE";

        -- Set to true if metadata need to be transported on independent MVB bus
        USE_MVB_META : boolean := TRUE;
        MVB_ITEMS    : natural := 1;

        MFB_REGIONS     : natural := 1;
        MFB_REGION_SIZE : natural := 8;
        MFB_BLOCK_SIZE  : natural := 8;
        MFB_ITEM_WIDTH  : natural := 8;

        HDR_META_WIDTH : natural := 24;

        RX_CHANNELS : natural := 8;
        TX_CHANNELS : natural := 8;

        USR_RX_PKT_SIZE_MAX : natural := 2**12;
        USR_TX_PKT_SIZE_MAX : natural := 2**12;

        -- If True, the MI bus is clocked on CLK signal and not MI_CLK
        MI_SAME_CLK : boolean := TRUE;
        -- Width of MI bus
        MI_WIDTH    : natural := 32
        );
    port(
        -- =======================================================================
        -- CLOCK AND RESET
        -- =======================================================================
        CLK   : in std_logic;
        RESET : in std_logic;

        -- =========================================================================================
        -- MVB+MFB towards DMA Engine
        -- =========================================================================================
        RX_MVB_META_PKT_SIZE_OUT : out std_logic_vector(MVB_ITEMS*log2(USR_RX_PKT_SIZE_MAX+1) -1 downto 0);
        RX_MVB_META_HDR_META_OUT : out std_logic_vector(MVB_ITEMS*HDR_META_WIDTH -1 downto 0);
        RX_MVB_META_CHAN_OUT     : out std_logic_vector(MVB_ITEMS*log2(RX_CHANNELS) -1 downto 0);
        RX_MVB_META_DISCARD_OUT  : out std_logic_vector(MVB_ITEMS -1 downto 0);
        RX_MVB_VLD_OUT           : out std_logic_vector(MVB_ITEMS -1 downto 0);
        RX_MVB_SRC_RDY_OUT       : out std_logic;
        RX_MVB_DST_RDY_OUT       : in  std_logic;

        RX_MFB_DATA_OUT    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF_OUT     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF_OUT     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS_OUT : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS_OUT : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY_OUT : out std_logic;
        RX_MFB_DST_RDY_OUT : in  std_logic;

        -- =========================================================================================
        -- MVB+MFB from the DMA Engine
        -- =========================================================================================
        TX_MVB_META_PKT_SIZE_IN : in  std_logic_vector(MVB_ITEMS*log2(USR_TX_PKT_SIZE_MAX+1) -1 downto 0);
        TX_MVB_META_HDR_META_IN : in  std_logic_vector(MVB_ITEMS*HDR_META_WIDTH -1 downto 0);
        TX_MVB_META_CHAN_IN     : in  std_logic_vector(MVB_ITEMS*log2(TX_CHANNELS) -1 downto 0);
        TX_MVB_VLD_IN           : in  std_logic_vector(MVB_ITEMS -1 downto 0);
        TX_MVB_SRC_RDY_IN       : in  std_logic;
        TX_MVB_DST_RDY_IN       : out std_logic;

        TX_MFB_DATA_IN    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF_IN     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF_IN     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS_IN : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS_IN : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY_IN : in  std_logic;
        TX_MFB_DST_RDY_IN : out std_logic;

        -- =========================================================================================
        -- MVB+MFB from application logic
        -- =========================================================================================
        RX_MVB_META_PKT_SIZE_IN : in  std_logic_vector(MVB_ITEMS*log2(USR_RX_PKT_SIZE_MAX+1) -1 downto 0);
        RX_MVB_META_HDR_META_IN : in  std_logic_vector(MVB_ITEMS*HDR_META_WIDTH -1 downto 0);
        RX_MVB_META_CHAN_IN     : in  std_logic_vector(MVB_ITEMS*log2(RX_CHANNELS) -1 downto 0);
        RX_MVB_META_DISCARD_IN  : in  std_logic_vector(MVB_ITEMS -1 downto 0);
        RX_MVB_VLD_IN           : in  std_logic_vector(MVB_ITEMS -1 downto 0);
        RX_MVB_SRC_RDY_IN       : in  std_logic;
        RX_MVB_DST_RDY_IN       : out std_logic;

        RX_MFB_DATA_IN    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF_IN     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF_IN     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS_IN : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS_IN : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY_IN : in  std_logic;
        RX_MFB_DST_RDY_IN : out std_logic;

        -- =========================================================================================
        -- MVB+MFB towards application logic
        -- =========================================================================================
        TX_MVB_META_PKT_SIZE_OUT : out std_logic_vector(MVB_ITEMS*log2(USR_RX_PKT_SIZE_MAX+1) -1 downto 0);
        TX_MVB_META_HDR_META_OUT : out std_logic_vector(MVB_ITEMS*HDR_META_WIDTH -1 downto 0);
        TX_MVB_META_CHAN_OUT     : out std_logic_vector(MVB_ITEMS*log2(RX_CHANNELS) -1 downto 0);
        TX_MVB_VLD_OUT           : out std_logic_vector(MVB_ITEMS -1 downto 0);
        TX_MVB_SRC_RDY_OUT       : out std_logic;
        TX_MVB_DST_RDY_OUT       : in  std_logic;

        TX_MFB_DATA_OUT    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF_OUT     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF_OUT     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS_OUT : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS_OUT : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
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

architecture FULL of DMA_LATENCY_METER is

    -- MI Asynchronous crossing
    signal mi_dwr_sync  : std_logic_vector(MI_WIDTH -1 downto 0);
    signal mi_addr_sync : std_logic_vector(MI_WIDTH -1 downto 0);
    signal mi_be_sync   : std_logic_vector(MI_WIDTH/8 -1 downto 0);
    signal mi_rd_sync   : std_logic;
    signal mi_wr_sync   : std_logic;
    signal mi_drd_sync  : std_logic_vector(MI_WIDTH-1 downto 0);
    signal mi_ardy_sync : std_logic;
    signal mi_drdy_sync : std_logic;

    -- =============================================================================================
    -- MFB Generator ----> MUX or METADATA_EXTRACTOR
    -- =============================================================================================
    signal mfb_data_gen    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH -1 downto 0);
    signal mfb_meta_gen    : std_logic_vector(log2(RX_CHANNELS) + log2(USR_RX_PKT_SIZE_MAX +1) -1 downto 0);
    signal mfb_sof_gen     : std_logic_vector(MFB_REGIONS -1 downto 0);
    signal mfb_eof_gen     : std_logic_vector(MFB_REGIONS -1 downto 0);
    signal mfb_sof_pos_gen : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)) -1 downto 0);
    signal mfb_eof_pos_gen : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
    signal mfb_src_rdy_gen : std_logic;
    signal mfb_dst_rdy_gen : std_logic;

    -- =============================================================================================
    -- METADATA_EXTRACTOR ---> MUX
    -- =============================================================================================
    signal rx_mvb_data_ext    : std_logic_vector(MVB_ITEMS*(log2(USR_RX_PKT_SIZE_MAX+1) + log2(RX_CHANNELS)) -1 downto 0);
    signal rx_mvb_vld_ext     : std_logic_vector(MVB_ITEMS -1 downto 0);
    signal rx_mvb_src_rdy_ext : std_logic;
    signal rx_mvb_dst_rdy_ext : std_logic;

    signal rx_mfb_data_ext    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH -1 downto 0);
    signal rx_mfb_meta_ext    : std_logic_vector(log2(RX_CHANNELS) + log2(USR_RX_PKT_SIZE_MAX +1) -1 downto 0);
    signal rx_mfb_sof_ext     : std_logic_vector(MFB_REGIONS -1 downto 0);
    signal rx_mfb_eof_ext     : std_logic_vector(MFB_REGIONS -1 downto 0);
    signal rx_mfb_sof_pos_ext : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)) -1 downto 0);
    signal rx_mfb_eof_pos_ext : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
    signal rx_mfb_src_rdy_ext : std_logic;
    signal rx_mfb_dst_rdy_ext : std_logic;

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
    -- Lanecy meters
    -- =============================================================================================
    constant TIMESTAMP_WIDTH  : positive := 11;
    constant LAT_PARAL_EVENTS : positive := 64;

    signal lat_meas_val_vld    : std_logic;
    signal lat_meas_val        : std_logic_vector(TIMESTAMP_WIDTH -1 downto 0);
    signal lat_meas_fifo_full  : std_logic;
    signal lat_meas_fifo_items : std_logic_vector(log2(LAT_PARAL_EVENTS) downto 0);

    type meas_fsm_state_t is (S_IDLE, S_COUNT_TESTING_PACKETS, S_TEST_FINISHED);
    signal meas_fsm_pst  : meas_fsm_state_t := S_IDLE;
    signal meas_fsm_nst  : meas_fsm_state_t := S_IDLE;
    signal pkt_cnt_pst   : unsigned(15 downto 0);
    signal pkt_cnt_nst   : unsigned(15 downto 0);
    signal test_finished : std_logic;

    -- =============================================================================================
    -- Miscelaneous
    -- =============================================================================================
    signal tst_gen_mux_sel   : std_logic;
    signal data_logger_rst   : std_logic;
    signal data_logger_ctrlo : std_logic_vector((1+1+log2(USR_RX_PKT_SIZE_MAX+1)+32+32+1) -1 downto 0);

    -- =============================================================================================
    -- Debug probes
    -- =============================================================================================
    -- attribute mark_debug : string;

    -- attribute mark_debug of data_logger_rst : signal is "true";
    -- attribute mark_debug of tst_gen_mux_sel : signal is "true";
    -- attribute mark_debug of meas_fsm_pst    : signal is "true";
    -- attribute mark_debug of pkt_cnt_pst     : signal is "true";
    -- attribute mark_debug of test_finished   : signal is "true";

    -- attribute mark_debug of mfb_gen_ctrl_pkt_cnt_clr : signal is "true";
    -- attribute mark_debug of mfb_gen_ctrl_length      : signal is "true";
    -- attribute mark_debug of mfb_gen_ctrl_chan_val    : signal is "true";
    -- attribute mark_debug of mfb_gen_ctrl_chan_inc    : signal is "true";
    -- attribute mark_debug of mfb_gen_ctrl_en          : signal is "true";
    -- attribute mark_debug of mfb_gen_ctrl_pkt_cnt     : signal is "true";

-- attribute mark_debug of lat_meas_val        : signal is "true";
-- attribute mark_debug of lat_meas_val_vld    : signal is "true";
-- attribute mark_debug of lat_meas_fifo_full  : signal is "true";
-- attribute mark_debug of lat_meas_fifo_items : signal is "true";
begin
    mi_async_g : if (not MI_SAME_CLK) generate
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
    else generate
        mi_addr_sync <= MI_ADDR;
        mi_dwr_sync  <= MI_DWR;
        mi_be_sync   <= MI_BE;
        mi_rd_sync   <= MI_RD;
        mi_wr_sync   <= MI_WR;
        MI_ARDY      <= mi_ardy_sync;
        MI_DRDY      <= mi_drdy_sync;
        MI_DRD       <= mi_drd_sync;
    end generate;

    TX_MVB_META_PKT_SIZE_OUT <= TX_MVB_META_PKT_SIZE_IN;
    TX_MVB_META_HDR_META_OUT <= TX_MVB_META_HDR_META_IN;
    TX_MVB_META_CHAN_OUT     <= TX_MVB_META_CHAN_IN;

    TX_MFB_DATA_OUT    <= TX_MFB_DATA_IN;
    TX_MFB_SOF_POS_OUT <= TX_MFB_SOF_POS_IN;
    TX_MFB_EOF_POS_OUT <= TX_MFB_EOF_POS_IN;
    TX_MFB_SOF_OUT     <= TX_MFB_SOF_IN;
    TX_MFB_EOF_OUT     <= TX_MFB_EOF_IN;
    TX_MFB_SRC_RDY_OUT <= TX_MFB_SRC_RDY_IN  when tst_gen_mux_sel = '0' else '0';
    TX_MFB_DST_RDY_IN  <= TX_MFB_DST_RDY_OUT when tst_gen_mux_sel = '0' else '1';

    use_tx_mvb_g : if (USE_MVB_META) generate
        TX_MVB_VLD_OUT     <= TX_MVB_VLD_IN;
        TX_MVB_SRC_RDY_OUT <= TX_MVB_SRC_RDY_IN  when tst_gen_mux_sel = '0' else '0';
        TX_MVB_DST_RDY_IN  <= TX_MVB_DST_RDY_OUT when tst_gen_mux_sel = '0' else '1';
    else generate
        TX_MVB_VLD_OUT     <= (others => '0');
        TX_MVB_SRC_RDY_OUT <= '0';
        TX_MVB_DST_RDY_IN  <= '1';
    end generate;

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

    data_logger_i : entity work.DATA_LOGGER
        generic map (
            MI_DATA_WIDTH => MI_WIDTH,
            MI_ADDR_WIDTH => MI_WIDTH,

            CNTER_CNT => 0,
            VALUE_CNT => 1,

            -- MUX for MFB Generator + all signals to control the generator
            CTRLO_WIDTH => data_logger_ctrlo'length,
            -- Counter
            CTRLI_WIDTH => 1+64+log2(LAT_PARAL_EVENTS)+1+1,

            CNTER_WIDTH => 64,
            VALUE_WIDTH => (others => TIMESTAMP_WIDTH),

            MIN_EN  => (others => TRUE),
            MAX_EN  => (others => TRUE),
            SUM_EN  => (others => FALSE),
            HIST_EN => (others => TRUE),

            SUM_EXTRA_WIDTH => (others => 16),
            HIST_BOX_CNT    => (others => 128),
            HIST_BOX_WIDTH  => (others => 32),
            CTRLO_DEFAULT   => (others => '0'))
        port map (
            CLK => CLK,
            RST => RESET,

            RST_DONE => open,
            SW_RST   => data_logger_rst,

            CTRLO => data_logger_ctrlo,
            CTRLI => (
                test_finished &
                mfb_gen_ctrl_pkt_cnt &
                lat_meas_fifo_items &
                lat_meas_fifo_full),

            CNTERS_INCR   => (others => '0'),
            CNTERS_SUBMIT => (others => '0'),
            CNTERS_DIFF   => (others => (others => '0')),

            VALUES_VLD => (others => lat_meas_val_vld),
            VALUES     => lat_meas_val,

            MI_DWR  => mi_dwr_sync,
            MI_ADDR => mi_addr_sync,
            MI_BE   => mi_be_sync,
            MI_RD   => mi_rd_sync,
            MI_WR   => mi_wr_sync,
            MI_ARDY => mi_ardy_sync,
            MI_DRD  => mi_drd_sync,
            MI_DRDY => mi_drdy_sync);

    latency_meter_i : entity work.LATENCY_METER
        generic map (
            DATA_WIDTH         => TIMESTAMP_WIDTH,
            MAX_PARALEL_EVENTS => LAT_PARAL_EVENTS,
            DEVICE             => DEVICE)
        port map (
            CLK => CLK,
            RST => RESET or data_logger_rst,

            START_EVENT => (or RX_MFB_SOF_OUT) and RX_MFB_SRC_RDY_OUT and RX_MFB_DST_RDY_OUT,
            END_EVENT   => (or TX_MFB_SOF_IN) and TX_MFB_SRC_RDY_IN and TX_MFB_DST_RDY_IN,

            LATENCY_VLD => lat_meas_val_vld,
            LATENCY     => lat_meas_val,

            FIFO_FULL  => lat_meas_fifo_full,
            FIFO_ITEMS => lat_meas_fifo_items);

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

    mfb_generator_i : entity work.MFB_GENERATOR
        generic map (
            REGIONS     => MFB_REGIONS,
            REGION_SIZE => MFB_REGION_SIZE,
            BLOCK_SIZE  => MFB_BLOCK_SIZE,
            ITEM_WIDTH  => MFB_ITEM_WIDTH,

            LENGTH_WIDTH   => log2(USR_RX_PKT_SIZE_MAX+1),
            CHANNELS_WIDTH => log2(RX_CHANNELS),

            PKT_CNT_WIDTH => 64,
            USE_PACP_ARCH => FALSE,
            DEVICE        => DEVICE)
        port map (
            CLK => CLK,
            RST => RESET or data_logger_rst,

            CTRL_EN          => mfb_gen_ctrl_en,
            CTRL_CHAN_INC    => mfb_gen_ctrl_chan_inc,
            CTRL_CHAN_VAL    => mfb_gen_ctrl_chan_val,
            CTRL_LENGTH      => mfb_gen_ctrl_length,
            CTRL_MAC_DST     => (others => '0'),
            CTRL_MAC_SRC     => (others => '0'),
            CTRL_PKT_CNT_CLR => mfb_gen_ctrl_pkt_cnt_clr,
            CTRL_PKT_CNT     => mfb_gen_ctrl_pkt_cnt,

            TX_MFB_DATA    => mfb_data_gen,
            TX_MFB_META    => mfb_meta_gen,
            TX_MFB_SOF     => mfb_sof_gen,
            TX_MFB_EOF     => mfb_eof_gen,
            TX_MFB_SOF_POS => mfb_sof_pos_gen,
            TX_MFB_EOF_POS => mfb_eof_pos_gen,
            TX_MFB_SRC_RDY => mfb_src_rdy_gen,
            TX_MFB_DST_RDY => mfb_dst_rdy_gen);

    use_rx_mvb_g : if (USE_MVB_META) generate
        mfb_gen_meta_ext_i : entity work.METADATA_EXTRACTOR
            generic map (
                MVB_ITEMS       => MVB_ITEMS,
                MFB_REGIONS     => MFB_REGIONS,
                MFB_REGION_SIZE => MFB_REGION_SIZE,
                MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,

                MFB_META_WIDTH => log2(USR_RX_PKT_SIZE_MAX+1) + log2(RX_CHANNELS),

                EXTRACT_MODE     => 0,
                MVB_SHAKEDOWN_EN => FALSE,
                OUT_MVB_PIPE_EN  => FALSE,
                OUT_MFB_PIPE_EN  => FALSE,
                DEVICE           => DEVICE)
            port map (
                CLK   => CLK,
                RESET => RESET,

                RX_MFB_DATA    => mfb_data_gen,
                RX_MFB_META    => mfb_meta_gen,
                RX_MFB_SOF     => mfb_sof_gen,
                RX_MFB_EOF     => mfb_eof_gen,
                RX_MFB_SOF_POS => mfb_sof_pos_gen,
                RX_MFB_EOF_POS => mfb_eof_pos_gen,
                RX_MFB_SRC_RDY => mfb_src_rdy_gen,
                RX_MFB_DST_RDY => mfb_dst_rdy_gen,

                TX_MVB_DATA    => rx_mvb_data_ext,
                TX_MVB_VLD     => rx_mvb_vld_ext,
                TX_MVB_SRC_RDY => rx_mvb_src_rdy_ext,
                TX_MVB_DST_RDY => rx_mvb_dst_rdy_ext,

                TX_MFB_DATA    => rx_mfb_data_ext,
                TX_MFB_META    => open,
                TX_MFB_SOF     => rx_mfb_sof_ext,
                TX_MFB_EOF     => rx_mfb_eof_ext,
                TX_MFB_SOF_POS => rx_mfb_sof_pos_ext,
                TX_MFB_EOF_POS => rx_mfb_eof_pos_ext,
                TX_MFB_SRC_RDY => rx_mfb_src_rdy_ext,
                TX_MFB_DST_RDY => rx_mfb_dst_rdy_ext);

        RX_MVB_META_PKT_SIZE_OUT <= RX_MVB_META_PKT_SIZE_IN when tst_gen_mux_sel = '0' else rx_mvb_data_ext(log2(USR_RX_PKT_SIZE_MAX+1) -1 downto 0);
        RX_MVB_META_HDR_META_OUT <= RX_MVB_META_HDR_META_IN when tst_gen_mux_sel = '0' else (others => '0');
        RX_MVB_META_CHAN_OUT     <= RX_MVB_META_CHAN_IN     when tst_gen_mux_sel = '0' else rx_mvb_data_ext(log2(RX_CHANNELS) + log2(USR_RX_PKT_SIZE_MAX+1) -1 downto log2(USR_RX_PKT_SIZE_MAX+1));
        RX_MVB_META_DISCARD_OUT  <= RX_MVB_META_DISCARD_IN  when tst_gen_mux_sel = '0' else (others => '0');
        RX_MVB_VLD_OUT           <= RX_MVB_VLD_IN           when tst_gen_mux_sel = '0' else rx_mvb_vld_ext;
        RX_MVB_SRC_RDY_OUT       <= RX_MVB_SRC_RDY_IN       when tst_gen_mux_sel = '0' else rx_mvb_src_rdy_ext;
        RX_MVB_DST_RDY_IN        <= RX_MVB_DST_RDY_OUT      when tst_gen_mux_sel = '0' else '1';
        rx_mvb_dst_rdy_ext       <= RX_MVB_DST_RDY_OUT      when tst_gen_mux_sel = '1' else '1';

        RX_MFB_DATA_OUT    <= RX_MFB_DATA_IN     when tst_gen_mux_sel = '0' else rx_mfb_data_ext;
        RX_MFB_SOF_OUT     <= RX_MFB_SOF_IN      when tst_gen_mux_sel = '0' else rx_mfb_sof_ext;
        RX_MFB_EOF_OUT     <= RX_MFB_EOF_IN      when tst_gen_mux_sel = '0' else rx_mfb_eof_ext;
        RX_MFB_SOF_POS_OUT <= RX_MFB_SOF_POS_IN  when tst_gen_mux_sel = '0' else rx_mfb_sof_pos_ext;
        RX_MFB_EOF_POS_OUT <= RX_MFB_EOF_POS_IN  when tst_gen_mux_sel = '0' else rx_mfb_eof_pos_ext;
        RX_MFB_SRC_RDY_OUT <= RX_MFB_SRC_RDY_IN  when tst_gen_mux_sel = '0' else rx_mfb_src_rdy_ext;
        RX_MFB_DST_RDY_IN  <= RX_MFB_DST_RDY_OUT when tst_gen_mux_sel = '0' else '1';
        rx_mfb_dst_rdy_ext <= RX_MFB_DST_RDY_OUT when tst_gen_mux_sel = '1' else '1';
    else generate
        RX_MVB_META_PKT_SIZE_OUT <= RX_MVB_META_PKT_SIZE_IN when tst_gen_mux_sel = '0' else mfb_meta_gen(log2(USR_RX_PKT_SIZE_MAX+1) -1 downto 0);
        RX_MVB_META_HDR_META_OUT <= RX_MVB_META_HDR_META_IN when tst_gen_mux_sel = '0' else (others => '0');
        RX_MVB_META_CHAN_OUT     <= RX_MVB_META_CHAN_IN     when tst_gen_mux_sel = '0' else mfb_meta_gen(log2(RX_CHANNELS) + log2(USR_RX_PKT_SIZE_MAX+1) -1 downto log2(USR_RX_PKT_SIZE_MAX+1));
        RX_MVB_META_DISCARD_OUT  <= RX_MVB_META_DISCARD_IN  when tst_gen_mux_sel = '0' else (others => '0');
        RX_MVB_VLD_OUT           <= (others => '0');
        RX_MVB_SRC_RDY_OUT       <= '0';
        RX_MVB_DST_RDY_IN        <= '1';

        RX_MFB_DATA_OUT    <= RX_MFB_DATA_IN     when tst_gen_mux_sel = '0' else mfb_data_gen;
        RX_MFB_SOF_OUT     <= RX_MFB_SOF_IN      when tst_gen_mux_sel = '0' else mfb_sof_gen;
        RX_MFB_EOF_OUT     <= RX_MFB_EOF_IN      when tst_gen_mux_sel = '0' else mfb_eof_gen;
        RX_MFB_SOF_POS_OUT <= RX_MFB_SOF_POS_IN  when tst_gen_mux_sel = '0' else mfb_sof_pos_gen;
        RX_MFB_EOF_POS_OUT <= RX_MFB_EOF_POS_IN  when tst_gen_mux_sel = '0' else mfb_eof_pos_gen;
        RX_MFB_SRC_RDY_OUT <= RX_MFB_SRC_RDY_IN  when tst_gen_mux_sel = '0' else mfb_src_rdy_gen;
        RX_MFB_DST_RDY_IN  <= RX_MFB_DST_RDY_OUT when tst_gen_mux_sel = '0' else '1';
        mfb_dst_rdy_gen    <= RX_MFB_DST_RDY_OUT when tst_gen_mux_sel = '1' else '1';
    end generate;
end architecture;
