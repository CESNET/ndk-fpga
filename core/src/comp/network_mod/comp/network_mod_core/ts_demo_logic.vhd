-- network_mod_core_etile.vhd: core of the Network module with Ethernet E-TILE(s).
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- This design file contains extra demo/testing logic for Timestamp Limiting (see the Timestamp Limiter unit).
-- The logic is enabled by the :vhdl:genconstant:`TS_DEMO_EN <network_mod_core.network_mod_core>` generic.
--
-- Works like this:
-- Timestamps and channel IDs are sent from the APP Core to the Network module via a special MVB-like interface.
-- There, before entering the IP core, time between packets from the same DMA channel is measured.
-- The measured data are stored in a couple of dedicated registers accessible over the MI (see address space below).
--
-- .. Warning::
--      The Demo/Testing logic works only for a single-channel (and single-Region) designs with E-Tile (Intel)!
--
-- **MI address space**
--
-- .. Note::
--
--     The Demo/Testing logic occupies address space after the MGMT unit.
--     It has never been tested with more than 1 channel.
--
-- +---------------------------------------+
-- | Register                   | Address  |
-- +============================+==========+
-- | reset_reg                  |   0x0    |
-- +----------------------------+----------+
-- | sample_reg                 |   0x4    |
-- +----------------------------+----------+
-- | packets_reg (low 32b)      |   0x8    |
-- +----------------------------+----------+
-- | packets_reg (high 32b)     |   0xC    |
-- +----------------------------+----------+
-- | ts_diffs_reg (low 32b)     |   0x10   |
-- +----------------------------+----------+
-- | ts_diffs_reg (high 32b)    |   0x14   |
-- +----------------------------+----------+
-- | ts_min_reg (low 32b)       |   0x18   |
-- +----------------------------+----------+
-- | ts_min_reg (high 32b)      |   0x1C   |
-- +----------------------------+----------+
-- | ts_max_reg (low 32b)       |   0x20   |
-- +----------------------------+----------+
-- | ts_max_reg (high 32b)      |   0x24   |
-- +----------------------------+----------+
-- | fifoxm_wr_err_reg          |   0x28   |
-- +----------------------------+----------+
-- | fifoxm_rd_err_reg          |   0x2C   |
-- +----------------------------+----------+
-- | asfifox_wr_err_reg         |   0x30   |
-- +----------------------------+----------+
-- | asfifox2_full_reg          |   0x34   |
-- +----------------------------+----------+
--
entity TS_DEMO_LOGIC is
generic(

    REGIONS           : natural := 1;

    ETH_PORT_CHAN     : natural := 8;

    MI_DATA_WIDTH     : natural := 32;
    MI_ADDR_WIDTH     : natural := 32;

    TX_DMA_CHANNELS   : natural := 8;

    -- Select correct FPGA device.
    -- "AGILEX", "STRATIX10", "ULTRASCALE", ...
    DEVICE            : string  := "STRATIX10"
);
port(
    -- =====================================================================
    -- CLOCK AND RESET
    -- =====================================================================
    CLK_ETH       : in  std_logic;
    RESET_ETH     : in  std_logic;

    MI_CLK        : in  std_logic;
    MI_RESET      : in  std_logic;

    -- =====================================================================
    -- RX interface (Packets for transmit to Ethernet)
    -- =====================================================================
    CORE_SOP      : in  std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    CORE_SRC_RDY  : in  std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    CORE_DST_RDY  : out std_logic_vector(ETH_PORT_CHAN-1 downto 0);

    APP_CHANNEL   : in  std_logic_vector(REGIONS*log2(TX_DMA_CHANNELS)-1 downto 0);
    APP_TIMESTAMP : in  std_logic_vector(REGIONS*48-1 downto 0);
    APP_VLD       : in  std_logic_vector(REGIONS-1 downto 0);

    TSU_TS_NS     : in  std_logic_vector(64-1 downto 0);
    TSU_TS_DV     : in  std_logic;

    -- =====================================================================
    -- MI interface
    -- =====================================================================
    MI_DWR        : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_ADDR       : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
    MI_RD         : in  std_logic;
    MI_WR         : in  std_logic;
    MI_BE         : in  std_logic_vector(MI_DATA_WIDTH/8-1 downto 0);
    MI_DRD        : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_ARDY       : out std_logic;
    MI_DRDY       : out std_logic
);
end entity;

architecture FULL of TS_DEMO_LOGIC is

    -- =========================================================================
    --                               CONSTANTS
    -- =========================================================================

    -- =========================================================================
    --                                SIGNALS
    -- =========================================================================

    signal app_channel_arr         : slv_array_t     (REGIONS-1 downto 0)(log2(TX_DMA_CHANNELS)-1 downto 0);
    signal app_timestamp_arr       : slv_array_t     (REGIONS-1 downto 0)(48-1 downto 0);
    signal fifoxm_din_arr             : slv_array_t     (REGIONS-1 downto 0)(log2(TX_DMA_CHANNELS)+48-1 downto 0);
    signal fifoxm_din                 : std_logic_vector(REGIONS*            log2(TX_DMA_CHANNELS)+48-1 downto 0);
    signal fifoxm_wr                  : std_logic_vector(REGIONS-1 downto 0);
    signal fifoxm_full                : std_logic;
    signal fifoxm_write_error         : std_logic;
    signal fifoxm_write_errors        : unsigned(32-1 downto 0);

    signal valid_sop                  : std_logic;
    signal fifoxm_rd                  : std_logic_vector(REGIONS-1 downto 0);
    signal fifoxm_empty               : std_logic_vector(REGIONS-1 downto 0);
    signal fifoxm_dout                : std_logic_vector(REGIONS*            log2(TX_DMA_CHANNELS)+48-1 downto 0);
    signal fifoxm_dout_arr            : slv_array_t     (REGIONS-1 downto 0)(log2(TX_DMA_CHANNELS)+48-1 downto 0);
    signal mvb_channel_arr            : u_array_t       (REGIONS-1 downto 0)(log2(TX_DMA_CHANNELS)-1 downto 0);
    signal mvb_ts_arr                 : u_array_t       (REGIONS-1 downto 0)(48-1 downto 0);
    signal fifoxm_read_error          : std_logic;
    signal fifoxm_read_errors         : unsigned(32-1 downto 0);

    signal tsu_ts_ns_reg              : std_logic_vector(64-1 downto 0);
    signal tsu_ts_dv_reg              : std_logic;
    signal tsu_ts_ns_reg_conv         : std_logic_vector(64-1 downto 0);
    signal tsu_ts_channel_arr_reg     : u_array_t(log2(TX_DMA_CHANNELS)-1 downto 0)(64-1 downto 0);
    signal tsu_ts_diff                : unsigned(64-1 downto 0);
    signal mvb_ts_channel_arr_reg     : u_array_t(log2(TX_DMA_CHANNELS)-1 downto 0)(48-1 downto 0);
    signal mvb_ts_diff                : unsigned(48-1 downto 0);

    signal wait_for_first_pkt         : std_logic_vector(TX_DMA_CHANNELS-1 downto 0);
    signal first_pkt                  : std_logic_vector(TX_DMA_CHANNELS-1 downto 0);
    signal not_first_valid_ts         : std_logic;

    signal ts_actual                  : unsigned(48-1 downto 0);
    signal ts_expected                : unsigned(48-1 downto 0);
    signal ts_valid                   : std_logic;

    signal final_ts_diff_signed          : signed          (48-1 downto 0);
    signal final_ts_diff                 : std_logic_vector(48-1 downto 0);
    signal asfifox_din                   : std_logic_vector(48-1 downto 0);
    signal asfifox_wr                    : std_logic;
    signal asfifox_full                  : std_logic;
    signal asfifox_wr_error              : std_logic;
    signal asfifox_rd                    : std_logic;
    signal asfifox_dout                  : std_logic_vector(48-1 downto 0);
    signal asfifox_empty                 : std_logic;
    signal final_ts_diff_synced          : unsigned(48-1 downto 0);
    signal final_ts_diff_synced_vld      : std_logic;

    signal diff_ge_vld                   : std_logic;
    signal diff_ge_2_12                  : std_logic;
    signal diff_ge_2_14                  : std_logic;
    signal diff_ge_2_16                  : std_logic;
    signal diff_ge_2_20                  : std_logic;
    signal diff_ge_2_24                  : std_logic;
    signal diff_ge_2_30                  : std_logic;

    signal asfifox2_din                  : std_logic_vector(4-1 downto 0);
    signal asfifox2_wr                   : std_logic;
    signal asfifox2_full                 : std_logic;
    signal asfifox2_rd                   : std_logic;
    signal asfifox2_dout                 : std_logic_vector(4-1 downto 0);
    signal asfifox2_empty                : std_logic;

    signal wait_for_first_ts_diff_synced : std_logic;
    signal first_ts_diff_synced          : std_logic;

    signal pkt_accum                     : unsigned(64-1 downto 0);
    signal ts_diff_accum                 : unsigned(64-1 downto 0);
    signal ts_diff_min                   : unsigned(64-1 downto 0);
    signal ts_diff_max                   : unsigned(64-1 downto 0);
    signal fifoxm_wr_errs                : unsigned(32-1 downto 0);
    signal fifoxm_rd_errs                : unsigned(32-1 downto 0);
    signal asfifox_wr_errs               : unsigned(32-1 downto 0);
    signal asfifox2_fulls                : unsigned(32-1 downto 0);

    signal demo_reset_cmd                : std_logic;
    signal demo_sample_cmd               : std_logic;
    signal demo_rd_pkts_lo_cmd           : std_logic;
    signal demo_rd_pkts_hi_cmd           : std_logic;
    signal demo_rd_ts_lo_cmd             : std_logic;
    signal demo_rd_ts_hi_cmd             : std_logic;
    signal demo_rd_ts_min_lo_cmd         : std_logic;
    signal demo_rd_ts_min_hi_cmd         : std_logic;
    signal demo_rd_ts_max_lo_cmd         : std_logic;
    signal demo_rd_ts_max_hi_cmd         : std_logic;
    signal demo_rd_fifoxm_wr_err_cmd     : std_logic;
    signal demo_rd_fifoxm_rd_err_cmd     : std_logic;
    signal demo_rd_asfifox_wr_err_cmd    : std_logic;
    signal demo_rd_asfifox2_full_cmd     : std_logic;

    signal demo_reset_reg                : std_logic;
    signal demo_reset_edge               : std_logic;
    signal demo_reset_pulse              : std_logic;
    signal sw_reset                      : std_logic;
    signal eth_reset                     : std_logic_vector(0 downto 0);
    signal accum_reset                   : std_logic;

    signal demo_pkts_reg                 : std_logic_vector(2*MI_DATA_WIDTH-1 downto 0);
    signal demo_ts_reg                   : std_logic_vector(2*MI_DATA_WIDTH-1 downto 0);
    signal demo_ts_min_reg               : std_logic_vector(2*MI_DATA_WIDTH-1 downto 0);
    signal demo_ts_max_reg               : std_logic_vector(2*MI_DATA_WIDTH-1 downto 0);
    signal fifoxm_wr_err_reg             : std_logic_vector(  MI_DATA_WIDTH-1 downto 0);
    signal fifoxm_rd_err_reg             : std_logic_vector(  MI_DATA_WIDTH-1 downto 0);
    signal asfifox_wr_err_reg            : std_logic_vector(  MI_DATA_WIDTH-1 downto 0);
    signal asfifox2_full_reg             : std_logic_vector(  MI_DATA_WIDTH-1 downto 0);

    signal demo_drd                      : std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    signal demo_drdy                     : std_logic;

    -- attribute preserve_for_debug : boolean;
    -- attribute preserve_for_debug of fifoxm_wr                     : signal is true;
    -- attribute preserve_for_debug of fifoxm_full                   : signal is true;
    -- attribute preserve_for_debug of fifoxm_write_error            : signal is true;
    -- attribute preserve_for_debug of fifoxm_write_errors           : signal is true;
    -- attribute preserve_for_debug of valid_sop                     : signal is true;
    -- attribute preserve_for_debug of fifoxm_rd                     : signal is true;
    -- attribute preserve_for_debug of fifoxm_empty                  : signal is true;
    -- attribute preserve_for_debug of fifoxm_read_error             : signal is true;
    -- attribute preserve_for_debug of fifoxm_read_errors            : signal is true;
    -- attribute preserve_for_debug of tsu_ts_diff                   : signal is true;
    -- attribute preserve_for_debug of mvb_ts_diff                   : signal is true;
    -- attribute preserve_for_debug of wait_for_first_pkt            : signal is true;
    -- attribute preserve_for_debug of first_pkt                     : signal is true;
    -- attribute preserve_for_debug of not_first_valid_ts            : signal is true;
    -- attribute preserve_for_debug of final_ts_diff_signed          : signal is true;
    -- attribute preserve_for_debug of final_ts_diff                 : signal is true;
    -- attribute preserve_for_debug of asfifox_wr                    : signal is true;
    -- attribute preserve_for_debug of asfifox_full                  : signal is true;
    -- attribute preserve_for_debug of asfifox_wr_error              : signal is true;
    -- attribute preserve_for_debug of asfifox_rd                    : signal is true;
    -- attribute preserve_for_debug of asfifox_empty                 : signal is true;
    -- attribute preserve_for_debug of final_ts_diff_synced          : signal is true;
    -- attribute preserve_for_debug of final_ts_diff_synced_vld      : signal is true;
    -- attribute preserve_for_debug of diff_ge_vld                   : signal is true;
    -- attribute preserve_for_debug of diff_ge_2_12                  : signal is true;
    -- attribute preserve_for_debug of diff_ge_2_14                  : signal is true;
    -- attribute preserve_for_debug of diff_ge_2_16                  : signal is true;
    -- attribute preserve_for_debug of diff_ge_2_20                  : signal is true;
    -- attribute preserve_for_debug of diff_ge_2_24                  : signal is true;
    -- attribute preserve_for_debug of diff_ge_2_30                  : signal is true;
    -- attribute preserve_for_debug of wait_for_first_ts_diff_synced : signal is true;
    -- attribute preserve_for_debug of first_ts_diff_synced          : signal is true;
    -- attribute preserve_for_debug of demo_reset_cmd                : signal is true;
    -- attribute preserve_for_debug of demo_sample_cmd               : signal is true;
    -- attribute preserve_for_debug of demo_rd_pkts_lo_cmd           : signal is true;
    -- attribute preserve_for_debug of demo_rd_pkts_hi_cmd           : signal is true;
    -- attribute preserve_for_debug of demo_rd_ts_lo_cmd             : signal is true;
    -- attribute preserve_for_debug of demo_rd_ts_hi_cmd             : signal is true;
    -- attribute preserve_for_debug of demo_rd_ts_min_lo_cmd         : signal is true;
    -- attribute preserve_for_debug of demo_rd_ts_min_hi_cmd         : signal is true;
    -- attribute preserve_for_debug of demo_rd_ts_max_lo_cmd         : signal is true;
    -- attribute preserve_for_debug of demo_rd_ts_max_hi_cmd         : signal is true;
    -- attribute preserve_for_debug of demo_rd_fifoxm_wr_err_cmd     : signal is true;
    -- attribute preserve_for_debug of demo_rd_fifoxm_rd_err_cmd     : signal is true;
    -- attribute preserve_for_debug of demo_rd_asfifox_wr_err_cmd    : signal is true;
    -- attribute preserve_for_debug of demo_rd_asfifox2_full_cmd     : signal is true;
    -- attribute preserve_for_debug of sw_reset                      : signal is true;
    -- attribute preserve_for_debug of eth_reset                     : signal is true;
    -- attribute preserve_for_debug of accum_reset                   : signal is true;
    -- attribute preserve_for_debug of demo_drd                      : signal is true;
    -- attribute preserve_for_debug of demo_drdy                     : signal is true;

begin

    -- --------------------------------------------------------
    -- Timestamps (48 bits) and their appropriate channels passed from the Application
    -- --------------------------------------------------------
    app_channel_arr   <= slv_array_deser(APP_CHANNEL, REGIONS);
    app_timestamp_arr <= slv_array_deser(APP_TIMESTAMP, REGIONS);
    demo_fifoxm_din_g : for r in 0 to REGIONS-1 generate
        fifoxm_din_arr(r) <= app_channel_arr(r) & app_timestamp_arr(r);
    end generate;
    fifoxm_din <= slv_array_ser(fifoxm_din_arr);
    fifoxm_wr  <= APP_VLD;

    fifoxm_i: entity work.FIFOX_MULTI
    generic map (
        DATA_WIDTH  => log2(TX_DMA_CHANNELS)+48,
        ITEMS       => 2048,
        WRITE_PORTS => REGIONS,
        READ_PORTS  => REGIONS,
        RAM_TYPE    => "AUTO",
        DEVICE      => DEVICE
    )
    port map (
        CLK         => CLK_ETH,
        RESET       => RESET_ETH,

        DI          => fifoxm_din,
        WR          => fifoxm_wr,
        FULL        => fifoxm_full,
        AFULL       => open,

        DO          => fifoxm_dout,
        RD          => fifoxm_rd,
        EMPTY       => fifoxm_empty,
        AEMPTY      => open
    );

    fifoxm_dout_arr <= slv_array_deser(fifoxm_dout, REGIONS);
    demo_fifoxm_dout_g : for r in 0 to REGIONS-1 generate
        mvb_channel_arr(r) <= unsigned(fifoxm_dout_arr(r)(log2(TX_DMA_CHANNELS)+48-1 downto 48));
        mvb_ts_arr     (r) <= unsigned(fifoxm_dout_arr(r)(                      48-1 downto  0));
    end generate;

    -- Watch out for the relation between CORE signals (ETH_PORT_CHAN-1:0) and the FIFOXM_RD signal (REGIONS-1:0)
    valid_sop <= '1' when (CORE_SOP(0) = '1') and (CORE_SRC_RDY(0) = '1') and (CORE_DST_RDY(0) = '1') else '0';
    fifoxm_rd(0) <= '1' when (valid_sop = '1') and (fifoxm_empty(0) = '0') else '0';

    -- Error report register
    fifoxm_read_error  <= '1' when (valid_sop = '1') and (fifoxm_empty(0) = '1') else '0';
    fifoxm_write_error <= '1' when (fifoxm_wr(0) = '1') and (fifoxm_full = '1')  else '0';
    process(CLK_ETH)
    begin
        if rising_edge(CLK_ETH) then
            if (fifoxm_read_error = '1') then
                fifoxm_read_errors <= fifoxm_read_errors + 1;
            end if;
            if (fifoxm_write_error = '1') then
                fifoxm_write_errors <= fifoxm_write_errors + 1;
            end if;
            if (RESET_ETH = '1') then
                fifoxm_read_errors  <= (others => '0');
                fifoxm_write_errors <= (others => '0');
            end if;
        end if;
    end process;

    -- --------------------------------------------------------
    -- TSU timestamp logic
    -- --------------------------------------------------------

    -- Timestamp (+ valid) register
    -- Store only valid values
    process(CLK_ETH)
    begin
        if rising_edge(CLK_ETH) then
            if (RESET_ETH = '1') then
                tsu_ts_ns_reg <= (others => '0');
            elsif (TSU_TS_DV = '1') then
                tsu_ts_ns_reg <= TSU_TS_NS;
            end if;
        end if;
    end process;

    -- TSU format to ns conversion
    tsu_format_to_ns_i : entity work.TSU_FORMAT_TO_NS
    generic map(
        REG_BITMAP => "111"
    )
    port map(
        CLK    => CLK_ETH           ,
        RESET  => RESET_ETH         ,
        TS_TSU => tsu_ts_ns_reg     ,
        TS_NS  => tsu_ts_ns_reg_conv
    );

    -- TSU TS store and compare logic per DMA channel
    tsu_ts_diff_channel_g : for ch in 0 to log2(TX_DMA_CHANNELS)-1 generate
        -- Store valid TSU TS into appropriate channels
        process(CLK_ETH)
        begin
            if rising_edge(CLK_ETH) then
                if (RESET_ETH = '1') or (sw_reset = '1') then
                    tsu_ts_channel_arr_reg(ch) <= (others => '0');
                elsif (fifoxm_rd(0) = '1') and (mvb_channel_arr(0) = ch) then
                    tsu_ts_channel_arr_reg(ch) <= unsigned(tsu_ts_ns_reg_conv);
                end if;
            end if;
        end process;

    end generate;

    -- Compare with the previously stored TSU TS (in the selected channel)
    tsu_ts_diff <= unsigned(tsu_ts_ns_reg_conv) - tsu_ts_channel_arr_reg(to_integer(mvb_channel_arr(0)));

    -- --------------------------------------------------------
    -- MVB timestamp logic
    -- --------------------------------------------------------
    -- TSU TS store and compare logic per DMA channel
    mvb_ts_diff_channel_g : for ch in 0 to log2(TX_DMA_CHANNELS)-1 generate
        -- Store valid TSU TS into appropriate channels
        process(CLK_ETH)
        begin
            if rising_edge(CLK_ETH) then
                if (RESET_ETH = '1') or (sw_reset = '1') then
                    mvb_ts_channel_arr_reg(ch) <= (others => '0');
                elsif (fifoxm_rd(0) = '1') and (mvb_channel_arr(0) = ch) then
                    mvb_ts_channel_arr_reg(ch) <= mvb_ts_arr(0);
                end if;
            end if;
        end process;
    end generate;

    -- Compare the new MVB TS with the previously stored in the selected channel
    mvb_ts_diff <= mvb_ts_arr(0) - mvb_ts_channel_arr_reg(to_integer(mvb_channel_arr(0)));


    -- --------------------------------------------------------
    -- First packet logic
    -- --------------------------------------------------------

    first_pkt_g : for ch in 0 to TX_DMA_CHANNELS-1 generate

        process(CLK_ETH)
        begin
            if rising_edge(CLK_ETH) then
                if (valid_sop = '1') and (fifoxm_empty(0) = '0') and (mvb_channel_arr(0) = ch) then
                    wait_for_first_pkt(ch) <= '0';
                end if;
                if (RESET_ETH = '1') or (sw_reset = '1') then
                    wait_for_first_pkt(ch) <= '1';
                end if;
            end if;
        end process;

        -- First packet after reset
        first_pkt(ch) <= '1' when (valid_sop = '1') and (fifoxm_empty(0) = '0') and (mvb_channel_arr(0) = ch) and (wait_for_first_pkt(ch) = '1') else '0';

    end generate;

    -- --------------------------------------------------------
    -- Clock domain crossing (CLK_ETH -> MI_CLK)
    -- --------------------------------------------------------

    -- A valid TS (packet), which is not the first
    not_first_valid_ts <= '1' when (fifoxm_rd(0) = '1') and (first_pkt(to_integer(mvb_channel_arr(0))) = '0') else '0';
    -- A register to avoid timing issues
    process(CLK_ETH)
    begin
        if rising_edge(CLK_ETH) then
            ts_actual   <= resize(tsu_ts_diff, 48);
            ts_expected <= mvb_ts_diff;
            ts_valid    <= not_first_valid_ts;
            if (RESET_ETH = '1') or (sw_reset = '1') then
                ts_actual   <= (others => '0');
                ts_expected <= (others => '0');
                ts_valid    <= '0';
            end if;
        end if;
    end process;

    -- Positive value = slacking behind schedule
    -- Negative value = ahead of schedule
    final_ts_diff_signed <= signed(ts_actual) - signed(ts_expected);
    -- Absolute value for complete deviation (=sum of deviations, positive as well as negative)
    final_ts_diff <= absolute2slv(final_ts_diff_signed);

    -- A register to avoid timing issues
    process(CLK_ETH)
    begin
        if rising_edge(CLK_ETH) then
            asfifox_din <= final_ts_diff;
            asfifox_wr  <= ts_valid;
            if (RESET_ETH = '1') or (sw_reset = '1') then
                asfifox_wr <= '0';
            end if;
        end if;
    end process;

    -- --------------------------------
    -- Signals for debug
    -- The measured difference is Greater or Equal to:
    diff_ge_2_12 <= or asfifox_din(47 downto 12);
    diff_ge_2_14 <= or asfifox_din(47 downto 14);
    diff_ge_2_16 <= or asfifox_din(47 downto 16);
    diff_ge_2_20 <= or asfifox_din(47 downto 20);
    diff_ge_2_24 <= or asfifox_din(47 downto 24);
    diff_ge_2_30 <= or asfifox_din(47 downto 30);

    diff_ge_vld <= (diff_ge_2_12 or
                    diff_ge_2_14 or
                    diff_ge_2_16 or
                    diff_ge_2_20 or
                    diff_ge_2_24 or
                    diff_ge_2_30) and asfifox_wr;
    -- --------------------------------

    asfifox_wr_error <= '1' when (asfifox_wr = '1') and (asfifox_full = '1') else '0';
    demo_asfifox_i : entity work.ASFIFOX
    generic map(
        DATA_WIDTH => 48    ,
        ITEMS      => 512   ,
        RAM_TYPE   => "LUT" ,
        FWFT_MODE  => true  ,
        OUTPUT_REG => true  ,
        DEVICE     => DEVICE
    )
    port map (
        WR_CLK    => CLK_ETH      ,
        WR_RST    => RESET_ETH    ,
        WR_DATA   => asfifox_din  ,
        WR_EN     => asfifox_wr   ,
        WR_FULL   => asfifox_full ,
        WR_AFULL  => open         ,
        WR_STATUS => open         ,

        RD_CLK    => MI_CLK   ,
        RD_RST    => MI_RESET ,
        RD_DATA   => asfifox_dout ,
        RD_EN     => asfifox_rd   ,
        RD_EMPTY  => asfifox_empty,
        RD_AEMPTY => open         ,
        RD_STATUS => open
    );

    asfifox_rd <= not accum_reset;

    final_ts_diff_synced      <= unsigned(asfifox_dout);
    final_ts_diff_synced_vld  <= not asfifox_empty;

    demo_asreset_i : entity work.ASYNC_RESET
    generic map(
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => 1
    )
    port map (
        CLK       => MI_CLK,
        ASYNC_RST => RESET_ETH,
        OUT_RST   => eth_reset
    );

    -- --------------------------------
    -- Error asfifox
    asfifox2_din <= fifoxm_write_error & -- failing to write a TS from the APP Core (is Full)
                    fifoxm_read_error  & -- failing to read when a packet (SOP) is passing (is Empty)
                    asfifox_wr_error   & -- failing to write the measured difference (is Full)
                    asfifox2_full;       -- failing to write one of the errors above (is Full)

    asfifox2_wr <= fifoxm_write_error or
                    fifoxm_read_error  or
                    asfifox_wr_error;

    demo_asfifox2_i : entity work.ASFIFOX
    generic map(
        DATA_WIDTH => 4     ,
        ITEMS      => 512   ,
        RAM_TYPE   => "LUT" ,
        FWFT_MODE  => true  ,
        OUTPUT_REG => true  ,
        DEVICE     => DEVICE
    )
    port map (
        WR_CLK    => CLK_ETH       ,
        WR_RST    => RESET_ETH     ,
        WR_DATA   => asfifox2_din  ,
        WR_EN     => asfifox2_wr   ,
        WR_FULL   => asfifox2_full ,
        WR_AFULL  => open          ,
        WR_STATUS => open          ,

        RD_CLK    => MI_CLK    ,
        RD_RST    => MI_RESET  ,
        RD_DATA   => asfifox2_dout ,
        RD_EN     => asfifox2_rd   ,
        RD_EMPTY  => asfifox2_empty,
        RD_AEMPTY => open          ,
        RD_STATUS => open
    );

    asfifox2_rd <= not accum_reset;

    -- --------------------------------------------------------
    -- Accumulation logic
    -- --------------------------------------------------------

    -- Accumulation of transmitted packets (SOFs)
    process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (accum_reset = '1') then
                pkt_accum <= (others => '0');
            elsif (final_ts_diff_synced_vld = '1') then
                pkt_accum <= pkt_accum + 1;
            end if;
        end if;
    end process;
    -- Accumulation of timestamp differences
    process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (accum_reset = '1') then
                ts_diff_accum <= (others => '0');
            elsif (final_ts_diff_synced_vld = '1') then
                ts_diff_accum <= ts_diff_accum + final_ts_diff_synced;
            end if;
        end if;
    end process;

    -- First packet logic (again)
    -- This time it is to get a real minimal value (otherwise would be stuck at 0 forever)
    process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (final_ts_diff_synced_vld = '1') then
                wait_for_first_ts_diff_synced <= '0';
            end if;
            if (accum_reset = '1') then
                wait_for_first_ts_diff_synced <= '1';
            end if;
        end if;
    end process;
    -- First packet after reset
    first_ts_diff_synced <= '1' when (final_ts_diff_synced_vld = '1') and (wait_for_first_ts_diff_synced = '1') else '0';

    -- Store the minimum deviation
    process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (accum_reset = '1') then
                ts_diff_min <= (others => '0');
            elsif (final_ts_diff_synced_vld = '1') and ((final_ts_diff_synced < ts_diff_min) or (first_ts_diff_synced = '1')) then
                ts_diff_min <= resize(final_ts_diff_synced, 64);
            end if;
        end if;
    end process;

    -- Store the maximum deviation
    process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (accum_reset = '1') then
                ts_diff_max <= (others => '0');
            elsif (final_ts_diff_synced_vld = '1') and (final_ts_diff_synced > ts_diff_max) then
                ts_diff_max <= resize(final_ts_diff_synced, 64);
            end if;
        end if;
    end process;

    -- Error registers -----------------------------------------
    process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (asfifox2_dout(3) = '1') and (asfifox2_empty = '0') then
                fifoxm_wr_errs <= fifoxm_wr_errs + 1;
            end if;
            if (asfifox2_dout(2) = '1') and (asfifox2_empty = '0') then
                fifoxm_rd_errs <= fifoxm_rd_errs + 1;
            end if;
            if (asfifox2_dout(1) = '1') and (asfifox2_empty = '0') then
                asfifox_wr_errs <= asfifox_wr_errs + 1;
            end if;
            if (asfifox2_dout(0) = '1') and (asfifox2_empty = '0') then
                asfifox2_fulls <= asfifox2_fulls + 1;
            end if;
            if (accum_reset = '1') then
                fifoxm_wr_errs  <= (others => '0');
                fifoxm_rd_errs  <= (others => '0');
                asfifox_wr_errs <= (others => '0');
                asfifox2_fulls  <= (others => '0');
            end if;
        end if;
    end process;


    -- --------------------------------------------------------
    -- MI logic
    -- --------------------------------------------------------

    MI_ARDY <= MI_WR or MI_RD;
    MI_DRD  <= demo_drd;
    MI_DRDY <= demo_drdy;

    -- Command resolution
    demo_reset_cmd             <= '1' when (MI_WR = '1') and (MI_ADDR(6 downto 2) = "00000") else '0'; -- 0x0
    demo_sample_cmd            <= '1' when (MI_WR = '1') and (MI_ADDR(6 downto 2) = "00001") else '0'; -- 0x4
    demo_rd_pkts_lo_cmd        <= '1' when (MI_RD = '1') and (MI_ADDR(6 downto 2) = "00010") else '0'; -- 0x8
    demo_rd_pkts_hi_cmd        <= '1' when (MI_RD = '1') and (MI_ADDR(6 downto 2) = "00011") else '0'; -- 0xC
    demo_rd_ts_lo_cmd          <= '1' when (MI_RD = '1') and (MI_ADDR(6 downto 2) = "00100") else '0'; -- 0x10
    demo_rd_ts_hi_cmd          <= '1' when (MI_RD = '1') and (MI_ADDR(6 downto 2) = "00101") else '0'; -- 0x14
    demo_rd_ts_min_lo_cmd      <= '1' when (MI_RD = '1') and (MI_ADDR(6 downto 2) = "00110") else '0'; -- 0x18
    demo_rd_ts_min_hi_cmd      <= '1' when (MI_RD = '1') and (MI_ADDR(6 downto 2) = "00111") else '0'; -- 0x1C
    demo_rd_ts_max_lo_cmd      <= '1' when (MI_RD = '1') and (MI_ADDR(6 downto 2) = "01000") else '0'; -- 0x20
    demo_rd_ts_max_hi_cmd      <= '1' when (MI_RD = '1') and (MI_ADDR(6 downto 2) = "01001") else '0'; -- 0x24
    demo_rd_fifoxm_wr_err_cmd  <= '1' when (MI_RD = '1') and (MI_ADDR(6 downto 2) = "01010") else '0'; -- 0x28
    demo_rd_fifoxm_rd_err_cmd  <= '1' when (MI_RD = '1') and (MI_ADDR(6 downto 2) = "01011") else '0'; -- 0x2C
    demo_rd_asfifox_wr_err_cmd <= '1' when (MI_RD = '1') and (MI_ADDR(6 downto 2) = "01100") else '0'; -- 0x30
    demo_rd_asfifox2_full_cmd  <= '1' when (MI_RD = '1') and (MI_ADDR(6 downto 2) = "01101") else '0'; -- 0x34

    -- Reset register
    process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (MI_RESET = '1') or (demo_reset_pulse = '1') then
                demo_reset_reg <= '0';
            end if;
            if (demo_reset_cmd = '1') then
                demo_reset_reg <= '1';
            end if;
        end if;
    end process;

    -- Detect rising edge
    edge_detect_i : entity work.EDGE_DETECT
    port map(
        CLK  => MI_CLK,
        DI   => demo_reset_reg,
        EDGE => demo_reset_edge
    );

    -- Use the detected edge to extend the reset pulse
    pulse_extend_i : entity work.PULSE_EXTEND
    generic map(
        N => 5
    )
    port map(
        RST => MI_RESET,
        CLK => MI_CLK,
        I   => demo_reset_edge,
        O   => demo_reset_pulse
    );

    sw_reset <= '1' when (demo_reset_pulse = '1') else '0';

    -- Reset for accumulators
    accum_reset <= eth_reset(0) or sw_reset or demo_sample_cmd;

    -- MI packet accumulation and TS accumulation registers (RO)
    -- Sample values of the accumulation registers
    process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (MI_RESET = '1') or (sw_reset = '1') then
                demo_pkts_reg      <= (others => '0');
                demo_ts_reg        <= (others => '0');
                demo_ts_min_reg    <= (others => '0');
                demo_ts_max_reg    <= (others => '0');
                fifoxm_wr_err_reg  <= (others => '0');
                fifoxm_rd_err_reg  <= (others => '0');
                asfifox_wr_err_reg <= (others => '0');
                asfifox2_full_reg  <= (others => '0');
            elsif (demo_sample_cmd = '1') then
                demo_pkts_reg      <= std_logic_vector(pkt_accum);
                demo_ts_reg        <= std_logic_vector(ts_diff_accum);
                demo_ts_min_reg    <= std_logic_vector(ts_diff_min);
                demo_ts_max_reg    <= std_logic_vector(ts_diff_max);
                fifoxm_wr_err_reg  <= std_logic_vector(fifoxm_wr_errs);
                fifoxm_rd_err_reg  <= std_logic_vector(fifoxm_rd_errs);
                asfifox_wr_err_reg <= std_logic_vector(asfifox_wr_errs);
                asfifox2_full_reg  <= std_logic_vector(asfifox2_fulls);
            end if;
        end if;
    end process;

    demo_drdy <= demo_rd_pkts_lo_cmd        or
                 demo_rd_pkts_hi_cmd        or
                 demo_rd_ts_lo_cmd          or
                 demo_rd_ts_hi_cmd          or
                 demo_rd_ts_min_lo_cmd      or
                 demo_rd_ts_min_hi_cmd      or
                 demo_rd_ts_max_lo_cmd      or
                 demo_rd_ts_max_hi_cmd      or
                 demo_rd_fifoxm_wr_err_cmd  or
                 demo_rd_fifoxm_rd_err_cmd  or
                 demo_rd_asfifox_wr_err_cmd or
                 demo_rd_asfifox2_full_cmd;

    demo_drd <= demo_pkts_reg     (MI_DATA_WIDTH  -1 downto             0) when (demo_rd_pkts_lo_cmd        = '1') else
                demo_pkts_reg     (MI_DATA_WIDTH*2-1 downto MI_DATA_WIDTH) when (demo_rd_pkts_hi_cmd        = '1') else

                demo_ts_reg       (MI_DATA_WIDTH  -1 downto             0) when (demo_rd_ts_lo_cmd          = '1') else
                demo_ts_reg       (MI_DATA_WIDTH*2-1 downto MI_DATA_WIDTH) when (demo_rd_ts_hi_cmd          = '1') else

                demo_ts_min_reg   (MI_DATA_WIDTH  -1 downto             0) when (demo_rd_ts_min_lo_cmd      = '1') else
                demo_ts_min_reg   (MI_DATA_WIDTH*2-1 downto MI_DATA_WIDTH) when (demo_rd_ts_min_hi_cmd      = '1') else

                demo_ts_max_reg   (MI_DATA_WIDTH  -1 downto             0) when (demo_rd_ts_max_lo_cmd      = '1') else
                demo_ts_max_reg   (MI_DATA_WIDTH*2-1 downto MI_DATA_WIDTH) when (demo_rd_ts_max_hi_cmd      = '1') else

                -- Error registers - not included in the Device Tree
                fifoxm_wr_err_reg (MI_DATA_WIDTH  -1 downto             0) when (demo_rd_fifoxm_wr_err_cmd  = '1') else
                fifoxm_rd_err_reg (MI_DATA_WIDTH  -1 downto             0) when (demo_rd_fifoxm_rd_err_cmd  = '1') else
                asfifox_wr_err_reg(MI_DATA_WIDTH  -1 downto             0) when (demo_rd_asfifox_wr_err_cmd = '1') else
                asfifox2_full_reg (MI_DATA_WIDTH  -1 downto             0) when (demo_rd_asfifox2_full_cmd  = '1') else

                (others => '0');

end architecture;
