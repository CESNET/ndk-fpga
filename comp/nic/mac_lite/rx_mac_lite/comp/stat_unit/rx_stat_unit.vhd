-- stat_unit.vhd: Statistics unit
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity RX_MAC_LITE_STAT_UNIT is
    generic (
        -- =====================================================================
        -- MFB CONFIGURATION:
        -- =====================================================================
        REGIONS            : natural := 4;
        REGION_SIZE        : natural := 8;
        BLOCK_SIZE         : natural := 8;
        ITEM_WIDTH         : natural := 8;
        -- =====================================================================
        -- OTHERS CONFIGURATION:
        -- =====================================================================
        INBANDFCS          : boolean := true;
        LEN_WIDTH          : natural := 14;
        CNT_IN_DSP         : boolean := true;
        DEVICE             : string  := "STRATIX10";
        -- Counters setup
        SIZE_EN            : boolean := true;
        LEN_HISTOGRAM_EN   : boolean := true
    );
    port (
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK                    : in  std_logic;
        RESET                  : in  std_logic;
        -- =====================================================================
        -- CONTROL INTERFACE
        -- =====================================================================
        -- Enable of statistics
        CTRL_STAT_EN           : in  std_logic;
        -- SW reset
        CTRL_SW_RESET          : in  std_logic;
        -- Take snapshot of counter
        CTRL_TAKE_SNAPSHOT     : in  std_logic;
        -- Read and release snapshot of counters
        CTRL_READ_SNAPSHOT     : in  std_logic;
        -- =====================================================================
        -- INPUT STATISTICS FLAGS
        -- =====================================================================
        -- Flag of received frame for each region
        IN_FRAME_RECEIVED      : in  std_logic_vector(REGIONS-1 downto 0);
        -- Flag of discarded frame for each region
        IN_FRAME_DISCARDED     : in  std_logic_vector(REGIONS-1 downto 0);
        -- Flag of discarded frame due to buffer overfull for each region
        IN_BUFFER_OVF          : in  std_logic_vector(REGIONS-1 downto 0);
        -- Flag of frame drop due to RX MAC is off for each region
        IN_FRAME_DROP_OFF      : in  std_logic_vector(REGIONS-1 downto 0);
        -- Flag of frame error (GMII errors) for each region
        IN_FRAME_ERROR_MASKED  : in  std_logic_vector(REGIONS-1 downto 0);
        -- Flag of frame with bad CRC for each region
        IN_CRC_ERROR           : in  std_logic_vector(REGIONS-1 downto 0);
        IN_CRC_ERROR_MASKED    : in  std_logic_vector(REGIONS-1 downto 0);
        -- Flag of frame with bad MAC for each region
        IN_MAC_ERROR           : in  std_logic_vector(REGIONS-1 downto 0);
        IN_MAC_ERROR_MASKED    : in  std_logic_vector(REGIONS-1 downto 0);
        -- Flag of length is below MinTU or over MaxTU for each region
        IN_LEN_ERROR_MASKED    : in  std_logic_vector(REGIONS-1 downto 0);
        -- Flag of Broadcast frame for each region
        IN_MAC_BCAST           : in  std_logic_vector(REGIONS-1 downto 0);
        -- Flag of Multicast frame for each region
        IN_MAC_MCAST           : in  std_logic_vector(REGIONS-1 downto 0);
        -- Frame lenght of received frames for each region
        IN_FRAME_LEN           : in  slv_array_t(REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
        -- Flag of length is below MIN for each region
        IN_LEN_BELOW_MIN       : in  std_logic_vector(REGIONS-1 downto 0);
        -- Flag of length is over MTU for each region
        IN_LEN_OVER_MTU        : in  std_logic_vector(REGIONS-1 downto 0);
        -- Valid of input statistics flags for each region
        IN_STAT_FLAGS_VLD      : in  std_logic_vector(REGIONS-1 downto 0);
        -- =====================================================================
        -- OUTPUT OF STATISTICS COUNTERS
        -- =====================================================================
        -- Output statistic are valid
        OUT_STAT_VLD           : out std_logic;
        -- Total number of total (RX) frames
        OUT_BASE_TOTAL         : out std_logic_vector(63 downto 0);
        -- Total number of passed (TX) frames
        OUT_BASE_PASSED        : out std_logic_vector(63 downto 0);
        -- Total number of discarded frames
        OUT_BASE_DROPPED       : out std_logic_vector(63 downto 0);
        -- Discarded frames due to RX MAC is disabled
        OUT_BASE_DROP_OFF      : out std_logic_vector(63 downto 0);
        -- Discarded frames due to buffer overflow
        OUT_BASE_DROP_OVF      : out std_logic_vector(63 downto 0);
        -- Discarded frames due to MAC filter
        OUT_BASE_DROP_FLT      : out std_logic_vector(63 downto 0);
        -- Discarded frames due to error
        OUT_BASE_DROP_ERR      : out std_logic_vector(63 downto 0);
        OUT_BASE_ERR_LEN       : out std_logic_vector(63 downto 0);
        OUT_BASE_ERR_MII       : out std_logic_vector(63 downto 0);
        OUT_BASE_ERR_CRC       : out std_logic_vector(63 downto 0);
        -- Total number of received bytes (including CRC)
        OUT_RX_BYTES           : out std_logic_vector(63 downto 0);
        -- Total number of transmitted bytes
        OUT_TX_BYTES           : out std_logic_vector(63 downto 0);
        -- Total number of received frames with bad CRC
        OUT_RFC_CRC_ERR        : out std_logic_vector(63 downto 0);
        -- Total number of received frames with bad MAC
        OUT_RFC_MAC_ERR        : out std_logic_vector(63 downto 0);
        -- Total number of received frames over MTU
        OUT_RFC_OVER_MTU       : out std_logic_vector(63 downto 0);
        -- Total number of received frames below minimal length
        OUT_RFC_BELOW_MIN      : out std_logic_vector(63 downto 0);
        -- Total number of received broadcast frames
        OUT_RFC_MAC_BCAST      : out std_logic_vector(63 downto 0);
        -- Total number of received multicast frames that were not
        -- identified as broadcast
        OUT_RFC_MAC_MCAST      : out std_logic_vector(63 downto 0);
        -- Total number of received "fragment" frames
        OUT_RFC_FRAGMENT       : out std_logic_vector(63 downto 0);
        -- Total number of received "jabber" frames (frames above 1518 bytes including CRC)
        OUT_RFC_JABBER         : out std_logic_vector(63 downto 0);
        -- Length histograms of received frames (including CRC)
        OUT_HIST_UNDERSIZE     : out std_logic_vector(63 downto 0);
        OUT_HIST_64            : out std_logic_vector(63 downto 0);
        OUT_HIST_65_127        : out std_logic_vector(63 downto 0);
        OUT_HIST_128_255       : out std_logic_vector(63 downto 0);
        OUT_HIST_256_511       : out std_logic_vector(63 downto 0);
        OUT_HIST_512_1023      : out std_logic_vector(63 downto 0);
        OUT_HIST_1024_1518     : out std_logic_vector(63 downto 0);
        OUT_HIST_OVER_1518     : out std_logic_vector(63 downto 0);
        OUT_HIST_1519_2047     : out std_logic_vector(63 downto 0);
        OUT_HIST_2048_4095     : out std_logic_vector(63 downto 0);
        OUT_HIST_4096_8191     : out std_logic_vector(63 downto 0);
        OUT_HIST_OVER_8191     : out std_logic_vector(63 downto 0)
    );
end entity;

architecture FULL of RX_MAC_LITE_STAT_UNIT is

    -- Quartus max fanout constraint
    attribute maxfan : integer;

    constant USE_DSP_CNT         : boolean := CNT_IN_DSP;
    constant SUM_ONE_OUTPUT_REG  : boolean := True;
    constant FRAME_STATS_W       : natural := 18;
    constant HIST_W              : natural := 12;

    signal s_fixed_frame_len           : u_array_t(REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal s_frame_below_64            : std_logic_vector(REGIONS-1 downto 0);
    signal s_frame_over_1518           : std_logic_vector(REGIONS-1 downto 0);

    signal s_reg_in_base_total         : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_base_passed        : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_base_dropped       : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_base_drop_off      : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_base_drop_ovf      : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_base_drop_flt      : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_base_drop_err      : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_base_err_len       : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_base_err_mii       : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_base_err_crc       : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_rfc_crc_err        : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_rfc_below_min      : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_rfc_over_mtu       : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_rfc_mac_err        : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_rfc_mac_mcast      : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_rfc_mac_bcast      : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_rfc_fragment       : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_rfc_jabber         : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_stat_vld           : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_frame_len          : u_array_t(REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);

    signal s_frame_stats_vld           : slv_array_t(FRAME_STATS_W-1 downto 0)(REGIONS-1 downto 0);
    signal s_frame_stats_inc           : slv_array_t(FRAME_STATS_W-1 downto 0)(log2(REGIONS+1)-1 downto 0);
    signal s_frame_stats_cnt           : slv_array_t(FRAME_STATS_W-1 downto 0)(63 downto 0);

    signal s_resized_rx_frame_len      : slv_array_t(REGIONS-1 downto 0)(LEN_WIDTH+1-1 downto 0);
    signal s_resized_rx_frame_len_vld  : std_logic_vector(REGIONS-1 downto 0);
    signal s_resized_tx_frame_len      : slv_array_t(REGIONS-1 downto 0)(LEN_WIDTH+1-1 downto 0);
    signal s_resized_tx_frame_len_vld  : std_logic_vector(REGIONS-1 downto 0);

    signal s_reset                     : std_logic;
    signal s_stat_en                   : std_logic;
    signal s_snapshot_en               : std_logic;

    signal s_cnt_sum_rx_frame_size_inc : std_logic_vector(LEN_WIDTH downto 0);
    signal s_cnt_sum_tx_frame_size_inc : std_logic_vector(LEN_WIDTH downto 0);
    signal s_cnt_sum_rx_frame_size     : std_logic_vector(63 downto 0);
    signal s_cnt_sum_tx_frame_size     : std_logic_vector(63 downto 0);

    signal s_size_hist_vld             : slv_array_t(HIST_W-1 downto 0)(REGIONS-1 downto 0);
    signal s_size_hist_inc             : slv_array_t(HIST_W-1 downto 0)(log2(REGIONS+1)-1 downto 0);
    signal s_size_hist_cnt             : slv_array_t(HIST_W-1 downto 0)(63 downto 0);

    attribute maxfan of s_snapshot_en  : signal is 16;

begin

    -- =========================================================================
    -- Input flags register
    -- =========================================================================

    frame_flags_g : for r in 0 to REGIONS-1 generate
        -- Prepare frame length (RFC defines frame length with CRC!)
        remove_crc_g : if not INBANDFCS generate
            s_fixed_frame_len(r) <= unsigned(IN_FRAME_LEN(r)) + 4;
        end generate;

        no_remove_crc_g : if INBANDFCS generate
            s_fixed_frame_len(r) <= unsigned(IN_FRAME_LEN(r));
        end generate;

        s_frame_below_64(r)  <= '1' when (s_fixed_frame_len(r) < 64) else '0';
        s_frame_over_1518(r) <= '1' when (s_fixed_frame_len(r) > 1518) else '0';
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_reg_in_base_total    <= IN_FRAME_RECEIVED;
            s_reg_in_base_passed   <= IN_FRAME_RECEIVED and not IN_FRAME_DISCARDED;
            s_reg_in_base_dropped  <= IN_FRAME_DISCARDED;
            s_reg_in_base_drop_off <= IN_FRAME_DROP_OFF;
            s_reg_in_base_drop_ovf <= IN_BUFFER_OVF;
            s_reg_in_base_drop_flt <= IN_MAC_ERROR_MASKED;
            s_reg_in_base_drop_err <= IN_LEN_ERROR_MASKED or IN_FRAME_ERROR_MASKED or IN_CRC_ERROR_MASKED;
            s_reg_in_base_err_len  <= IN_LEN_ERROR_MASKED;
            s_reg_in_base_err_mii  <= IN_FRAME_ERROR_MASKED;
            s_reg_in_base_err_crc  <= IN_CRC_ERROR_MASKED;
            s_reg_in_rfc_crc_err   <= IN_CRC_ERROR;
            s_reg_in_rfc_below_min <= IN_LEN_BELOW_MIN;
            s_reg_in_rfc_over_mtu  <= IN_LEN_OVER_MTU;
            s_reg_in_rfc_mac_err   <= IN_MAC_ERROR;
            s_reg_in_rfc_mac_mcast <= IN_MAC_MCAST;
            s_reg_in_rfc_mac_bcast <= IN_MAC_BCAST;
            s_reg_in_rfc_fragment  <= IN_CRC_ERROR and s_frame_below_64;
            s_reg_in_rfc_jabber    <= IN_CRC_ERROR and s_frame_over_1518;
            s_reg_in_frame_len     <= s_fixed_frame_len;
        end if;
    end process;

    in_flags_vld_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_in_stat_vld <= (others => '0');
            else
                s_reg_in_stat_vld <= IN_STAT_FLAGS_VLD;
            end if;
        end if;
    end process;

    -- =========================================================================
    -- Control signals
    -- =========================================================================

    s_stat_en <= CTRL_STAT_EN;

    cnt_reset_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_reset <= RESET or CTRL_SW_RESET;
        end if;
    end process;

    snapshot_en_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_snapshot_en <= '0';
            elsif (CTRL_TAKE_SNAPSHOT = '1') then
                s_snapshot_en <= '1';
            elsif (CTRL_READ_SNAPSHOT = '1') then
                s_snapshot_en <= '0';
            end if;
        end if;
    end process;

    OUT_STAT_VLD <= s_snapshot_en;

    -- =========================================================================
    -- Frame Counters
    -- =========================================================================

    s_frame_stats_vld(0)  <= s_reg_in_base_total;
    s_frame_stats_vld(1)  <= s_reg_in_base_passed;
    s_frame_stats_vld(2)  <= s_reg_in_base_dropped;
    s_frame_stats_vld(3)  <= s_reg_in_base_drop_off;
    s_frame_stats_vld(4)  <= s_reg_in_base_drop_ovf;
    s_frame_stats_vld(5)  <= s_reg_in_base_drop_flt;
    s_frame_stats_vld(6)  <= s_reg_in_base_drop_err;
    s_frame_stats_vld(7)  <= s_reg_in_base_err_len;
    s_frame_stats_vld(8)  <= s_reg_in_base_err_mii;
    s_frame_stats_vld(9)  <= s_reg_in_base_err_crc;
    s_frame_stats_vld(10) <= s_reg_in_rfc_crc_err;
    s_frame_stats_vld(11) <= s_reg_in_rfc_mac_err;
    s_frame_stats_vld(12) <= s_reg_in_rfc_mac_mcast;
    s_frame_stats_vld(13) <= s_reg_in_rfc_mac_bcast;
    s_frame_stats_vld(14) <= s_reg_in_rfc_below_min;
    s_frame_stats_vld(15) <= s_reg_in_rfc_over_mtu;
    s_frame_stats_vld(16) <= s_reg_in_rfc_fragment;
    s_frame_stats_vld(17) <= s_reg_in_rfc_jabber;

    frame_stats_g : for ii in 0 to FRAME_STATS_W-1 generate
        inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,

            DIN      => s_frame_stats_vld(ii),
            DIN_MASK => s_reg_in_stat_vld,
            DIN_VLD  => '1',

            DOUT     => s_frame_stats_inc(ii),
            DOUT_VLD => open
        );

        cnt_i : entity work.DSP_COUNTER
        generic map (
            INPUT_WIDTH  => log2(REGIONS+1),
            OUTPUT_WIDTH => 64,
            INPUT_REGS   => true,
            DEVICE       => DEVICE,
            DSP_ENABLE   => USE_DSP_CNT
        )
        port map (
            CLK        => CLK,
            CLK_EN     => s_stat_en,
            RESET      => s_reset,
            INCREMENT  => s_frame_stats_inc(ii),
            MAX_VAL    => (others => '1'),
            RESULT     => s_frame_stats_cnt(ii)
        );
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_snapshot_en = '0') then
                OUT_BASE_TOTAL    <= s_frame_stats_cnt(0);
                OUT_BASE_PASSED   <= s_frame_stats_cnt(1);
                OUT_BASE_DROPPED  <= s_frame_stats_cnt(2);
                OUT_BASE_DROP_OFF <= s_frame_stats_cnt(3);
                OUT_BASE_DROP_OVF <= s_frame_stats_cnt(4);
                OUT_BASE_DROP_FLT <= s_frame_stats_cnt(5);
                OUT_BASE_DROP_ERR <= s_frame_stats_cnt(6);
                OUT_BASE_ERR_LEN  <= s_frame_stats_cnt(7);
                OUT_BASE_ERR_MII  <= s_frame_stats_cnt(8);
                OUT_BASE_ERR_CRC  <= s_frame_stats_cnt(9);
                OUT_RFC_CRC_ERR   <= s_frame_stats_cnt(10);
                OUT_RFC_MAC_ERR   <= s_frame_stats_cnt(11);
                OUT_RFC_MAC_MCAST <= s_frame_stats_cnt(12);
                OUT_RFC_MAC_BCAST <= s_frame_stats_cnt(13);
                OUT_RFC_BELOW_MIN <= s_frame_stats_cnt(14);
                OUT_RFC_OVER_MTU  <= s_frame_stats_cnt(15);
                OUT_RFC_FRAGMENT  <= s_frame_stats_cnt(16);
                OUT_RFC_JABBER    <= s_frame_stats_cnt(17);
            end if;
        end if;
    end process;

    -- =========================================================================
    -- Counters: Sum received size
    -- =========================================================================

    size_g : if SIZE_EN generate
        -- sum received frame size ---------------------------------------------
        resized_rx_frame_len_g : for r in 0 to REGIONS-1 generate
            s_resized_rx_frame_len(r) <= std_logic_vector(resize(s_reg_in_frame_len(r),LEN_WIDTH+1));
        end generate;
        s_resized_rx_frame_len_vld <= s_reg_in_base_total and s_reg_in_stat_vld;

        cnt_sum_rx_frame_size_inc_i : entity work.PIPE_TREE_ADDER
        generic map (
            ITEMS      => REGIONS,
            DATA_WIDTH => LEN_WIDTH+1,
            LATENCY    => 1
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            IN_DATA  => slv_array_ser(s_resized_rx_frame_len,REGIONS,LEN_WIDTH+1),
            IN_VLD   => s_resized_rx_frame_len_vld,
            OUT_DATA => s_cnt_sum_rx_frame_size_inc(LEN_WIDTH downto 0)
        );

        cnt_sum_rx_frame_size_i : entity work.DSP_COUNTER
        generic map (
            INPUT_WIDTH  => LEN_WIDTH+1,
            OUTPUT_WIDTH => 64,
            INPUT_REGS   => true,
            DEVICE       => DEVICE,
            DSP_ENABLE   => USE_DSP_CNT
        )
        port map (
            CLK        => CLK,
            CLK_EN     => s_stat_en,
            RESET      => s_reset,
            INCREMENT  => s_cnt_sum_rx_frame_size_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_sum_rx_frame_size
        );

        -- sum transmitted frame size ------------------------------------------
        resized_tx_frame_len_g : for r in 0 to REGIONS-1 generate
            s_resized_tx_frame_len(r) <= std_logic_vector(resize(s_reg_in_frame_len(r),LEN_WIDTH+1));
        end generate;
        s_resized_tx_frame_len_vld <= s_reg_in_base_passed and s_reg_in_stat_vld;

        cnt_sum_tx_frame_size_inc_i : entity work.PIPE_TREE_ADDER
        generic map (
            ITEMS      => REGIONS,
            DATA_WIDTH => LEN_WIDTH+1,
            LATENCY    => 1
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            IN_DATA  => slv_array_ser(s_resized_tx_frame_len,REGIONS,LEN_WIDTH+1),
            IN_VLD   => s_resized_tx_frame_len_vld,
            OUT_DATA => s_cnt_sum_tx_frame_size_inc(LEN_WIDTH downto 0)
        );

        cnt_sum_tx_frame_size_i : entity work.DSP_COUNTER
        generic map (
            INPUT_WIDTH  => LEN_WIDTH+1,
            OUTPUT_WIDTH => 64,
            INPUT_REGS   => true,
            DEVICE       => DEVICE,
            DSP_ENABLE   => USE_DSP_CNT
        )
        port map (
            CLK        => CLK,
            CLK_EN     => s_stat_en,
            RESET      => s_reset,
            INCREMENT  => s_cnt_sum_tx_frame_size_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_sum_tx_frame_size
        );

        -- Register ------------------------------------------------------------
        size_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_snapshot_en = '0') then
                    OUT_RX_BYTES <= s_cnt_sum_rx_frame_size;
                    OUT_TX_BYTES <= s_cnt_sum_tx_frame_size;
                end if;
            end if;
        end process;

    end generate;

    no_size_g : if not SIZE_EN generate
        OUT_RX_BYTES <= (others => '0');
        OUT_TX_BYTES <= (others => '0');
    end generate;

    -- =========================================================================
    -- Counters: Frames length histograms
    -- =========================================================================

    len_hist_g : if LEN_HISTOGRAM_EN generate
        frame_sizes_g : for r in 0 to REGIONS-1 generate
            s_size_hist_vld(0)(r)  <= '1' when (s_reg_in_frame_len(r) < 64) else '0';
            s_size_hist_vld(1)(r)  <= '1' when (s_reg_in_frame_len(r) = 64) else '0';
            s_size_hist_vld(2)(r)  <= '1' when (s_reg_in_frame_len(r) >= 65 and s_reg_in_frame_len(r) <= 127) else '0';
            s_size_hist_vld(3)(r)  <= '1' when (s_reg_in_frame_len(r) >= 128 and s_reg_in_frame_len(r) <= 255) else '0';
            s_size_hist_vld(4)(r)  <= '1' when (s_reg_in_frame_len(r) >= 256 and s_reg_in_frame_len(r) <= 511) else '0';
            s_size_hist_vld(5)(r)  <= '1' when (s_reg_in_frame_len(r) >= 512 and s_reg_in_frame_len(r) <= 1023) else '0';
            s_size_hist_vld(6)(r)  <= '1' when (s_reg_in_frame_len(r) >= 1024 and s_reg_in_frame_len(r) <= 1518) else '0';
            s_size_hist_vld(7)(r)  <= '1' when (s_reg_in_frame_len(r) > 1518) else '0';
            s_size_hist_vld(8)(r)  <= '1' when (s_reg_in_frame_len(r) >= 1519 and s_reg_in_frame_len(r) <= 2047) else '0';
            s_size_hist_vld(9)(r)  <= '1' when (s_reg_in_frame_len(r) >= 2048 and s_reg_in_frame_len(r) <= 4095) else '0';
            s_size_hist_vld(10)(r) <= '1' when (s_reg_in_frame_len(r) >= 4096 and s_reg_in_frame_len(r) <= 8191) else '0';
            s_size_hist_vld(11)(r) <= '1' when (s_reg_in_frame_len(r) > 8191) else '0';
        end generate;

        hist_g : for ii in 0 to HIST_W-1 generate
            inc_i : entity work.SUM_ONE
            generic map (
                INPUT_WIDTH  => REGIONS,
                OUTPUT_WIDTH => log2(REGIONS+1),
                OUTPUT_REG   => SUM_ONE_OUTPUT_REG
            )
            port map (
                CLK      => CLK,
                RESET    => s_reset,

                DIN      => s_size_hist_vld(ii),
                DIN_MASK => s_reg_in_stat_vld,
                DIN_VLD  => '1',

                DOUT     => s_size_hist_inc(ii),
                DOUT_VLD => open
            );

            cnt_i : entity work.DSP_COUNTER
            generic map (
                INPUT_WIDTH  => log2(REGIONS+1),
                OUTPUT_WIDTH => 64,
                INPUT_REGS   => true,
                DEVICE       => DEVICE,
                DSP_ENABLE   => USE_DSP_CNT
            )
            port map (
                CLK        => CLK,
                CLK_EN     => s_stat_en,
                RESET      => s_reset,
                INCREMENT  => s_size_hist_inc(ii),
                MAX_VAL    => (others => '1'),
                RESULT     => s_size_hist_cnt(ii)
            );
        end generate;

        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_snapshot_en = '0') then
                    OUT_HIST_UNDERSIZE <= s_size_hist_cnt(0);
                    OUT_HIST_64        <= s_size_hist_cnt(1);
                    OUT_HIST_65_127    <= s_size_hist_cnt(2);
                    OUT_HIST_128_255   <= s_size_hist_cnt(3);
                    OUT_HIST_256_511   <= s_size_hist_cnt(4);
                    OUT_HIST_512_1023  <= s_size_hist_cnt(5);
                    OUT_HIST_1024_1518 <= s_size_hist_cnt(6);
                    OUT_HIST_OVER_1518 <= s_size_hist_cnt(7);
                    OUT_HIST_1519_2047 <= s_size_hist_cnt(8);
                    OUT_HIST_2048_4095 <= s_size_hist_cnt(9);
                    OUT_HIST_4096_8191 <= s_size_hist_cnt(10);
                    OUT_HIST_OVER_8191 <= s_size_hist_cnt(11);
                end if;
            end if;
        end process;
    end generate;

    no_len_hist_g : if not LEN_HISTOGRAM_EN generate
        OUT_HIST_UNDERSIZE <= (others => '0');
        OUT_HIST_64        <= (others => '0');
        OUT_HIST_65_127    <= (others => '0');
        OUT_HIST_128_255   <= (others => '0');
        OUT_HIST_256_511   <= (others => '0');
        OUT_HIST_512_1023  <= (others => '0');
        OUT_HIST_1024_1518 <= (others => '0');
        OUT_HIST_OVER_1518 <= (others => '0');
        OUT_HIST_1519_2047 <= (others => '0');
        OUT_HIST_2048_4095 <= (others => '0');
        OUT_HIST_4096_8191 <= (others => '0');
        OUT_HIST_OVER_8191 <= (others => '0');
    end generate;

end architecture;
