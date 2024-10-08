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
    generic(
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
        CRC_EN             : boolean := true;
        MAC_EN             : boolean := true;
        MTU_EN             : boolean := true;
        SIZE_EN            : boolean := true;
        BCAST_MCAST_EN     : boolean := true;
        FRAGMENT_JABBER_EN : boolean := true;
        LEN_HISTOGRAM_EN   : boolean := true
    );
    port(
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
        -- Flag of frame error (GMII errors) for each region
        IN_FRAME_ERROR         : in  std_logic_vector(REGIONS-1 downto 0);
        -- Flag of frame with bad CRC for each region
        IN_CRC_ERROR           : in  std_logic_vector(REGIONS-1 downto 0);
        -- Flag of frame with bad MAC for each region
        IN_MAC_ERROR           : in  std_logic_vector(REGIONS-1 downto 0);
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
        -- Total number of received frames
        OUT_FRAMES_RECEIVED    : out std_logic_vector(63 downto 0);
        -- Total number of transmitted frames
        OUT_FRAMES_TRANSMITTED : out std_logic_vector(63 downto 0);
        -- Total number of discarded frames
        OUT_FRAMES_DISCARDED   : out std_logic_vector(63 downto 0);
        -- Discarded frames due to buffer overflow
        OUT_BUFFER_OVF         : out std_logic_vector(63 downto 0);
        -- Total number of received bytes (including CRC)
        OUT_RX_BYTES           : out std_logic_vector(63 downto 0);
        -- Total number of transmitted bytes
        OUT_TX_BYTES           : out std_logic_vector(63 downto 0);
        -- Total number of received frames with bad CRC
        OUT_CRC_ERR            : out std_logic_vector(63 downto 0);
        -- Total number of received frames with bad MAC
        OUT_MAC_ERR            : out std_logic_vector(63 downto 0);
        -- Total number of received frames over MTU
        OUT_OVER_MTU           : out std_logic_vector(63 downto 0);
        -- Total number of received frames below minimal length
        OUT_BELOW_MIN          : out std_logic_vector(63 downto 0);
        -- Total number of received broadcast frames
        OUT_BCAST_FRAMES       : out std_logic_vector(63 downto 0);
        -- Total number of received multicast frames that were not
        -- identified as broadcast
        OUT_MCAST_FRAMES       : out std_logic_vector(63 downto 0);
        -- Total number of received "fragment" frames
        OUT_FRAGMENT_FRAMES    : out std_logic_vector(63 downto 0);
        -- Total number of received "jabber" frames (frames above 1518 bytes including CRC)
        OUT_JABBER_FRAMES      : out std_logic_vector(63 downto 0);
        -- Length histograms of received frames (including CRC)
        OUT_FRAMES_UNDERSIZE   : out std_logic_vector(63 downto 0);
        OUT_FRAMES_64          : out std_logic_vector(63 downto 0);
        OUT_FRAMES_65_127      : out std_logic_vector(63 downto 0);
        OUT_FRAMES_128_255     : out std_logic_vector(63 downto 0);
        OUT_FRAMES_256_511     : out std_logic_vector(63 downto 0);
        OUT_FRAMES_512_1023    : out std_logic_vector(63 downto 0);
        OUT_FRAMES_1024_1518   : out std_logic_vector(63 downto 0);
        OUT_FRAMES_OVER_1518   : out std_logic_vector(63 downto 0)
    );
end entity;

architecture FULL of RX_MAC_LITE_STAT_UNIT is

    -- Quartus max fanout constraint
    attribute maxfan : integer;

    constant DEVICE_WITH_DSP_CNT : boolean := (DEVICE = "7SERIES") or (DEVICE = "ULTRASCALE") or (DEVICE = "STRATIX10");
    constant USE_DSP_CNT         : boolean := CNT_IN_DSP and DEVICE_WITH_DSP_CNT;
    constant SUM_ONE_OUTPUT_REG  : boolean := True;

    type uns_array_t is array (natural range <>) of unsigned;

    signal s_reg_in_frame_received     : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_frame_transmitted  : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_frame_discarded    : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_buffer_ovf         : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_frame_error        : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_crc_error          : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_mac_error          : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_mac_bcast          : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_mac_mcast          : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_frame_len          : slv_array_t(REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal s_reg_in_len_below_min      : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_len_over_mtu       : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg_in_stat_flags_vld     : std_logic_vector(REGIONS-1 downto 0);

    signal s_fixed_frame_len           : uns_array_t(REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal s_resized_rx_frame_len      : slv_array_t(REGIONS-1 downto 0)(LEN_WIDTH+1-1 downto 0);
    signal s_resized_rx_frame_len_vld  : std_logic_vector(REGIONS-1 downto 0);
    signal s_resized_tx_frame_len      : slv_array_t(REGIONS-1 downto 0)(LEN_WIDTH+1-1 downto 0);
    signal s_resized_tx_frame_len_vld  : std_logic_vector(REGIONS-1 downto 0);

    signal s_reset                     : std_logic;
    signal s_stat_en                   : std_logic;
    signal s_snapshot_en               : std_logic;

    signal s_frame_received_inc        : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_frame_transmitted_inc     : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_frame_discarded_inc       : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_buffer_ovf_inc            : std_logic_vector(log2(REGIONS+1)-1 downto 0);

    signal s_cnt_frame_received        : std_logic_vector(63 downto 0);
    signal s_cnt_frame_transmitted     : std_logic_vector(63 downto 0);
    signal s_cnt_frame_discarded       : std_logic_vector(63 downto 0);
    signal s_cnt_buff_ovf_traff        : std_logic_vector(63 downto 0);

    signal s_crc_error_inc             : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_mac_error_inc             : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_len_below_min_inc         : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_len_over_mtu_inc          : std_logic_vector(log2(REGIONS+1)-1 downto 0);

    signal s_cnt_crc_errors            : std_logic_vector(63 downto 0);
    signal s_cnt_mac_errors            : std_logic_vector(63 downto 0);
    signal s_cnt_frames_below_min      : std_logic_vector(63 downto 0);
    signal s_cnt_frames_over_mtu       : std_logic_vector(63 downto 0);

    signal s_cnt_sum_rx_frame_size_inc : std_logic_vector(LEN_WIDTH downto 0);

    signal s_cnt_sum_tx_frame_size_inc : std_logic_vector(LEN_WIDTH downto 0);
    signal s_cnt_sum_rx_frame_size     : std_logic_vector(63 downto 0);
    signal s_cnt_sum_tx_frame_size     : std_logic_vector(63 downto 0);

    signal s_bcast_inc                 : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_mcast_inc                 : std_logic_vector(log2(REGIONS+1)-1 downto 0);

    signal s_cnt_mcast_frames          : std_logic_vector(63 downto 0);
    signal s_cnt_bcast_frames          : std_logic_vector(63 downto 0);

    signal s_frame_over_1518           : std_logic_vector(REGIONS-1 downto 0);
    signal s_fragment_frames           : std_logic_vector(REGIONS-1 downto 0);
    signal s_jabber_frames             : std_logic_vector(REGIONS-1 downto 0);

    signal s_fragment_frames_inc       : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_jabber_frames_inc         : std_logic_vector(log2(REGIONS+1)-1 downto 0);

    signal s_cnt_fragment_frames       : std_logic_vector(63 downto 0);
    signal s_cnt_jabber_frames         : std_logic_vector(63 downto 0);

    signal s_frames_64                 : std_logic_vector(REGIONS-1 downto 0);
    signal s_frames_65_127             : std_logic_vector(REGIONS-1 downto 0);
    signal s_frames_128_255            : std_logic_vector(REGIONS-1 downto 0);
    signal s_frames_256_511            : std_logic_vector(REGIONS-1 downto 0);
    signal s_frames_512_1023           : std_logic_vector(REGIONS-1 downto 0);
    signal s_frames_1024_1518          : std_logic_vector(REGIONS-1 downto 0);
    signal s_frames_over_1518          : std_logic_vector(REGIONS-1 downto 0);
    signal s_frames_undersize          : std_logic_vector(REGIONS-1 downto 0);

    signal s_frames_64_inc             : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_frames_65_127_inc         : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_frames_128_255_inc        : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_frames_256_511_inc        : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_frames_512_1023_inc       : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_frames_1024_1518_inc      : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_frames_over_1518_inc      : std_logic_vector(log2(REGIONS+1)-1 downto 0);
    signal s_frames_undersize_inc      : std_logic_vector(log2(REGIONS+1)-1 downto 0);

    signal s_cnt_frames_64             : std_logic_vector(63 downto 0);
    signal s_cnt_frames_65_127         : std_logic_vector(63 downto 0);
    signal s_cnt_frames_128_255        : std_logic_vector(63 downto 0);
    signal s_cnt_frames_256_511        : std_logic_vector(63 downto 0);
    signal s_cnt_frames_512_1023       : std_logic_vector(63 downto 0);
    signal s_cnt_frames_1024_1518      : std_logic_vector(63 downto 0);
    signal s_cnt_frames_over_1518      : std_logic_vector(63 downto 0);
    signal s_cnt_frames_undersize      : std_logic_vector(63 downto 0);

    attribute maxfan of s_snapshot_en  : signal is 16;

begin

    -- =========================================================================
    -- Input flags register
    -- =========================================================================

    in_flags_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_reg_in_frame_received    <= IN_FRAME_RECEIVED;
            s_reg_in_frame_transmitted <= IN_FRAME_RECEIVED and not IN_FRAME_DISCARDED;
            s_reg_in_frame_discarded   <= IN_FRAME_DISCARDED;
            s_reg_in_buffer_ovf        <= IN_BUFFER_OVF;
            s_reg_in_frame_error       <= IN_FRAME_ERROR;
            s_reg_in_crc_error         <= IN_CRC_ERROR;
            s_reg_in_mac_error         <= IN_MAC_ERROR;
            s_reg_in_mac_bcast         <= IN_MAC_BCAST;
            s_reg_in_mac_mcast         <= IN_MAC_MCAST and not IN_MAC_BCAST;
            s_reg_in_frame_len         <= IN_FRAME_LEN;
            s_reg_in_len_below_min     <= IN_LEN_BELOW_MIN;
            s_reg_in_len_over_mtu      <= IN_LEN_OVER_MTU;
        end if;
    end process;

    in_flags_vld_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_in_stat_flags_vld <= (others => '0');
            else
                s_reg_in_stat_flags_vld <= IN_STAT_FLAGS_VLD;
            end if;
        end if;
    end process;

    frame_len_g : for r in 0 to REGIONS-1 generate
        -- Prepare frame length (RFC defines frame length with CRC!)
        remove_crc_g : if not INBANDFCS generate
            s_fixed_frame_len(r) <= unsigned(s_reg_in_frame_len(r)) + 4;
        end generate;

        no_remove_crc_g : if INBANDFCS generate
            s_fixed_frame_len(r) <= unsigned(s_reg_in_frame_len(r));
        end generate;
    end generate;

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
    -- Counters: Received & Received & Discarded
    -- =========================================================================

    -- Received frames ---------------------------------------------------------
    frame_received_inc_i : entity work.SUM_ONE
    generic map (
        INPUT_WIDTH  => REGIONS,
        OUTPUT_WIDTH => log2(REGIONS+1),
        OUTPUT_REG   => SUM_ONE_OUTPUT_REG
    )
    port map (
        CLK      => CLK,
        RESET    => s_reset,
        -- Input ports
        DIN      => s_reg_in_frame_received,
        DIN_MASK => s_reg_in_stat_flags_vld,
        DIN_VLD  => '1',
        -- Output ports
        DOUT     => s_frame_received_inc,
        DOUT_VLD => open
    );

    cnt_frame_received_i : entity work.DSP_COUNTER
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
        INCREMENT  => s_frame_received_inc,
        MAX_VAL    => (others => '1'),
        RESULT     => s_cnt_frame_received
    );

    -- Transmitted frames ------------------------------------------------------
    frame_transmitted_inc_i : entity work.SUM_ONE
    generic map (
        INPUT_WIDTH  => REGIONS,
        OUTPUT_WIDTH => log2(REGIONS+1),
        OUTPUT_REG   => SUM_ONE_OUTPUT_REG
    )
    port map (
        CLK      => CLK,
        RESET    => s_reset,
        -- Input ports
        DIN      => s_reg_in_frame_transmitted,
        DIN_MASK => s_reg_in_stat_flags_vld,
        DIN_VLD  => '1',
        -- Output ports
        DOUT     => s_frame_transmitted_inc,
        DOUT_VLD => open
    );

    cnt_frame_transmitted_i : entity work.DSP_COUNTER
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
        INCREMENT  => s_frame_transmitted_inc,
        MAX_VAL    => (others => '1'),
        RESULT     => s_cnt_frame_transmitted
    );

    -- Discarded frames --------------------------------------------------------
    frame_discarded_inc_i : entity work.SUM_ONE
    generic map (
        INPUT_WIDTH  => REGIONS,
        OUTPUT_WIDTH => log2(REGIONS+1),
        OUTPUT_REG   => SUM_ONE_OUTPUT_REG
    )
    port map (
        CLK      => CLK,
        RESET    => s_reset,
        -- Input ports
        DIN      => s_reg_in_frame_discarded,
        DIN_MASK => s_reg_in_stat_flags_vld,
        DIN_VLD  => '1',
        -- Output ports
        DOUT     => s_frame_discarded_inc,
        DOUT_VLD => open
    );

    cnt_frame_discarded_i : entity work.DSP_COUNTER
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
        INCREMENT  => s_frame_discarded_inc,
        MAX_VAL    => (others => '1'),
        RESULT     => s_cnt_frame_discarded
    );

    -- Buffer overflow ---------------------------------------------------------
    buffer_ovf_inc_i : entity work.SUM_ONE
    generic map (
        INPUT_WIDTH  => REGIONS,
        OUTPUT_WIDTH => log2(REGIONS+1),
        OUTPUT_REG   => SUM_ONE_OUTPUT_REG
    )
    port map (
        CLK      => CLK,
        RESET    => s_reset,
        -- Input ports
        DIN      => s_reg_in_buffer_ovf,
        DIN_MASK => s_reg_in_stat_flags_vld,
        DIN_VLD  => '1',
        -- Output ports
        DOUT     => s_buffer_ovf_inc,
        DOUT_VLD => open
    );

    cnt_buff_ovf_traff_i : entity work.DSP_COUNTER
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
        INCREMENT  => s_buffer_ovf_inc,
        MAX_VAL    => (others => '1'),
        RESULT     => s_cnt_buff_ovf_traff
    );

    -- Register ----------------------------------------------------------------
    trafic_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_snapshot_en = '0') then
                OUT_FRAMES_RECEIVED    <= s_cnt_frame_received;
                OUT_FRAMES_TRANSMITTED <= s_cnt_frame_transmitted;
                OUT_FRAMES_DISCARDED   <= s_cnt_frame_discarded;
                OUT_BUFFER_OVF         <= s_cnt_buff_ovf_traff;
            end if;
        end if;
    end process;

    -- =========================================================================
    -- Counters: CRC & MTU & MAC
    -- =========================================================================

    -- CRC errors --------------------------------------------------------------
    crc_g : if CRC_EN generate
        crc_error_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_reg_in_crc_error,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_crc_error_inc,
            DOUT_VLD => open
        );

        cnt_crc_errors_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_crc_error_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_crc_errors
        );
    end generate;

    no_crc_g : if not CRC_EN generate
        s_cnt_crc_errors <= (others => '0');
    end generate;

    -- MAC errors --------------------------------------------------------------
    mac_g : if MAC_EN generate
        mac_error_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_reg_in_mac_error,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_mac_error_inc,
            DOUT_VLD => open
        );

        cnt_mac_errors_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_mac_error_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_mac_errors
        );
    end generate;

    no_mac_g : if not MAC_EN generate
        s_cnt_mac_errors <= (others => '0');
    end generate;

    -- MTU errors --------------------------------------------------------------
    mtu_g : if MTU_EN generate
        -- MIN
        len_below_min_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_reg_in_len_below_min,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_len_below_min_inc,
            DOUT_VLD => open
        );

        cnt_frames_below_min_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_len_below_min_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_frames_below_min
        );

        -- MAX
        len_over_mtu_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_reg_in_len_over_mtu,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_len_over_mtu_inc,
            DOUT_VLD => open
        );

        cnt_frames_over_mtu_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_len_over_mtu_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_frames_over_mtu
        );
    end generate;

    no_mtu_g : if not MTU_EN generate
        s_cnt_frames_below_min <= (others => '0');
        s_cnt_frames_over_mtu  <= (others => '0');
    end generate;

    -- Register ----------------------------------------------------------------
    errors_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_snapshot_en = '0') then
                OUT_CRC_ERR   <= s_cnt_crc_errors;
                OUT_MAC_ERR   <= s_cnt_mac_errors;
                OUT_BELOW_MIN <= s_cnt_frames_below_min;
                OUT_OVER_MTU  <= s_cnt_frames_over_mtu;
            end if;
        end if;
    end process;

    -- =========================================================================
    -- Counters: Sum received size
    -- =========================================================================

    size_g : if SIZE_EN generate
        -- sum received frame size ---------------------------------------------
        resized_rx_frame_len_g : for r in 0 to REGIONS-1 generate
            s_resized_rx_frame_len(r) <= std_logic_vector(resize(s_fixed_frame_len(r),LEN_WIDTH+1));
        end generate;
        s_resized_rx_frame_len_vld <= s_reg_in_frame_received and s_reg_in_stat_flags_vld;

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
            s_resized_tx_frame_len(r) <= std_logic_vector(resize(s_fixed_frame_len(r),LEN_WIDTH+1));
        end generate;
        s_resized_tx_frame_len_vld <= s_reg_in_frame_transmitted and s_reg_in_stat_flags_vld;

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
        OUT_RX_BYTES <= (others=>'0');
        OUT_TX_BYTES <= (others=>'0');
    end generate;

    -- =========================================================================
    -- Counters: Multicast and broadcast
    -- =========================================================================

    cast_g : if BCAST_MCAST_EN generate
        -- MAC BCAST -----------------------------------------------------------
        bcast_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_reg_in_mac_bcast,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_bcast_inc,
            DOUT_VLD => open
        );

        cnt_bcast_frames_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_bcast_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_bcast_frames
        );

        -- MAC MCAST -----------------------------------------------------------
        mcast_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_reg_in_mac_mcast,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_mcast_inc,
            DOUT_VLD => open
        );

        cnt_mcast_frames_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_mcast_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_mcast_frames
        );

        -- Register ------------------------------------------------------------
        cast_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_snapshot_en = '0') then
                OUT_MCAST_FRAMES <= s_cnt_mcast_frames;
                OUT_BCAST_FRAMES <= s_cnt_bcast_frames;
                end if;
            end if;
        end process;

    end generate;

    no_cast_g : if not BCAST_MCAST_EN generate
        OUT_MCAST_FRAMES <= (others=>'0');
        OUT_BCAST_FRAMES <= (others=>'0');
    end generate;

    -- =========================================================================
    -- Counters: Fragment and Jabber
    -- =========================================================================

    fragment_jabber_g : if FRAGMENT_JABBER_EN generate
        frame_over_1518_g : for r in 0 to REGIONS-1 generate
            s_frame_over_1518(r) <= '1' when (s_fixed_frame_len(r) > 1518) else '0';
        end generate;

        s_fragment_frames <= s_reg_in_crc_error and s_reg_in_len_below_min;
        s_jabber_frames   <= s_reg_in_crc_error and s_frame_over_1518;

        -- Fragment ------------------------------------------------------------
        fragment_frames_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_fragment_frames,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_fragment_frames_inc,
            DOUT_VLD => open
        );

        cnt_fragment_frames_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_fragment_frames_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_fragment_frames
        );

        -- Jabber --------------------------------------------------------------
        jabber_frames_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_jabber_frames,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_jabber_frames_inc,
            DOUT_VLD => open
        );

        cnt_jabber_frames_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_jabber_frames_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_jabber_frames
        );

        -- Register ------------------------------------------------------------
        fragment_jabber_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_snapshot_en = '0') then
                OUT_FRAGMENT_FRAMES <= s_cnt_fragment_frames;
                OUT_JABBER_FRAMES   <= s_cnt_jabber_frames;
                end if;
            end if;
        end process;
    end generate;

    no_fragment_jabber_g : if not FRAGMENT_JABBER_EN generate
        OUT_FRAGMENT_FRAMES <= (others=>'0');
        OUT_JABBER_FRAMES   <= (others=>'0');
    end generate;

    -- =========================================================================
    -- Counters: Frames length histograms
    -- =========================================================================

    len_hist_g : if LEN_HISTOGRAM_EN generate
        frame_sizes_g : for r in 0 to REGIONS-1 generate
            s_frames_64(r)        <= '1' when (s_fixed_frame_len(r) = 64) else '0';
            s_frames_65_127(r)    <= '1' when (s_fixed_frame_len(r) >= 65 and s_fixed_frame_len(r) <= 127) else '0';
            s_frames_128_255(r)   <= '1' when (s_fixed_frame_len(r) >= 128 and s_fixed_frame_len(r) <= 255) else '0';
            s_frames_256_511(r)   <= '1' when (s_fixed_frame_len(r) >= 256 and s_fixed_frame_len(r) <= 511) else '0';
            s_frames_512_1023(r)  <= '1' when (s_fixed_frame_len(r) >= 512 and s_fixed_frame_len(r) <= 1023) else '0';
            s_frames_1024_1518(r) <= '1' when (s_fixed_frame_len(r) >= 1024 and s_fixed_frame_len(r) <= 1518) else '0';
            s_frames_over_1518(r) <= '1' when (s_fixed_frame_len(r) > 1518) else '0';
            s_frames_undersize(r) <= '1' when (s_fixed_frame_len(r) < 64) else '0';
        end generate;

        -- frames 64 -----------------------------------------------------------
        frames_64_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_frames_64,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_frames_64_inc,
            DOUT_VLD => open
        );

        cnt_frames_64_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_frames_64_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_frames_64
        );

        -- frames 65 127 -------------------------------------------------------
        frames_65_127_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_frames_65_127,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_frames_65_127_inc,
            DOUT_VLD => open
        );

        cnt_frames_65_127_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_frames_65_127_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_frames_65_127
        );

        -- frames 128 255 ------------------------------------------------------
        frames_128_255_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_frames_128_255,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_frames_128_255_inc,
            DOUT_VLD => open
        );

        cnt_frames_128_255_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_frames_128_255_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_frames_128_255
        );

        -- frames 256 511 ------------------------------------------------------
        frames_256_511_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_frames_256_511,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_frames_256_511_inc,
            DOUT_VLD => open
        );

        cnt_frames_256_511_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_frames_256_511_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_frames_256_511
        );

        -- frames 512 1023 -----------------------------------------------------
        frames_512_1023_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_frames_512_1023,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_frames_512_1023_inc,
            DOUT_VLD => open
        );

        cnt_frames_512_1023_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_frames_512_1023_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_frames_512_1023
        );

        -- frames 1024 1518 ----------------------------------------------------
        frames_1024_1518_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_frames_1024_1518,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_frames_1024_1518_inc,
            DOUT_VLD => open
        );

        cnt_frames_1024_1518_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_frames_1024_1518_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_frames_1024_1518
        );

        -- frames over 1518 ----------------------------------------------------
        frames_over_1518_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_frames_over_1518,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_frames_over_1518_inc,
            DOUT_VLD => open
        );

        cnt_frames_over_1518_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_frames_over_1518_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_frames_over_1518
        );

        -- frames under 64 -----------------------------------------------------
        frames_undersize_inc_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH  => REGIONS,
            OUTPUT_WIDTH => log2(REGIONS+1),
            OUTPUT_REG   => SUM_ONE_OUTPUT_REG
        )
        port map (
            CLK      => CLK,
            RESET    => s_reset,
            -- Input ports
            DIN      => s_frames_undersize,
            DIN_MASK => s_reg_in_stat_flags_vld,
            DIN_VLD  => '1',
            -- Output ports
            DOUT     => s_frames_undersize_inc,
            DOUT_VLD => open
        );

        cnt_frames_undersize_i : entity work.DSP_COUNTER
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
            INCREMENT  => s_frames_undersize_inc,
            MAX_VAL    => (others => '1'),
            RESULT     => s_cnt_frames_undersize
        );

        -- Register ------------------------------------------------------------
        len_hist_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_snapshot_en = '0') then
                    OUT_FRAMES_64        <= s_cnt_frames_64;
                    OUT_FRAMES_65_127    <= s_cnt_frames_65_127;
                    OUT_FRAMES_128_255   <= s_cnt_frames_128_255;
                    OUT_FRAMES_256_511   <= s_cnt_frames_256_511;
                    OUT_FRAMES_512_1023  <= s_cnt_frames_512_1023;
                    OUT_FRAMES_1024_1518 <= s_cnt_frames_1024_1518;
                    OUT_FRAMES_OVER_1518 <= s_cnt_frames_over_1518;
                    OUT_FRAMES_UNDERSIZE <= s_cnt_frames_undersize;
                end if;
            end if;
        end process;
    end generate;

    no_len_hist_g : if not LEN_HISTOGRAM_EN generate
        OUT_FRAMES_64        <= (others=>'0');
        OUT_FRAMES_65_127    <= (others=>'0');
        OUT_FRAMES_128_255   <= (others=>'0');
        OUT_FRAMES_256_511   <= (others=>'0');
        OUT_FRAMES_512_1023  <= (others=>'0');
        OUT_FRAMES_1024_1518 <= (others=>'0');
        OUT_FRAMES_OVER_1518 <= (others=>'0');
        OUT_FRAMES_UNDERSIZE <= (others=>'0');
    end generate;

end architecture;
