-- pcie_core_debug.vhd: PCIe debug module
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- ============================================================================
--                                Description
-- ============================================================================

-- This is the debug PCIe core module.
-- It contains a number of debug components.
-- Streaming Debug Probes monitor SRC and DST RDY signals and and Event Counters monitor the number of available PCIe credits for each Hard IP core.
-- They are controlled over the MI interface.
--
-- **MI address space**
--
-- +----------------+----------------+------------------------------------------------------------------------------------------------+
-- | Hard IP | Component                                                                                            | Address range   |
-- +=========+======================================================================================================+=================+
-- |         | Streaming Debug (Master with one or two Probe(s))                                                    |   0x00 - 0x3F   |
-- +         +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x40 - 0x4F   |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x50 - 0x5F   |
-- +         | Event Counter(s) - signal: PCIe credits of Posted HEADERS     +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0x60 - 0x6F   |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-255  |   0x70 - 0x7F   |
-- +         +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x80 - 0x8F   |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x90 - 0x9F   |
-- +         | Event Counter(s) - signal: PCIe credits of Posted DATA        +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0xA0 - 0xAF   |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-4095 |   0xB0 - 0xBF   |
-- +    0    +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0xC0 - 0xCF   |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0xD0 - 0xDF   |
-- +         | Event Counter(s) - signal: PCIe credits of Non-Posted HEADERS +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0xE0 - 0xEF   |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-255  |   0xF0 - 0xFF   |
-- +         +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x100 - 0x10F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x110 - 0x11F |
-- +         | Event Counter(s) - signal: PCIe credits of Non-Posted DATA    +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0x120 - 0x12F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-4095 |   0x130 - 0x13F |
-- +---------+------------------------------------------------------------------------------------------------------+-----------------+
-- |         | Streaming Debug (Master with one or two Probe(s))                                                    |   0x140 - 0x17F |
-- +         +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x180 - 0x18F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x190 - 0x19F |
-- +         | Event Counter(s) - signal: PCIe credits of Posted HEADERS     +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0x1A0 - 0x1AF |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-255  |   0x1B0 - 0x1BF |
-- +         +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x1C0 - 0x1CF |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x1D0 - 0x1DF |
-- +         | Event Counter(s) - signal: PCIe credits of Posted DATA        +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0x1E0 - 0x1EF |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-4095 |   0x1F0 - 0x1FF |
-- +    1    +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x200 - 0x20F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x210 - 0x21F |
-- +         | Event Counter(s) - signal: PCIe credits of Non-Posted HEADERS +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0x220 - 0x22F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-255  |   0x230 - 0x23F |
-- +         +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x240 - 0x24F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x250 - 0x25F |
-- +         | Event Counter(s) - signal: PCIe credits of Non-Posted DATA    +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0x260 - 0x26F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-4095 |   0x270 - 0x27F |
-- +---------+------------------------------------------------------------------------------------------------------+-----------------+
--
entity PCIE_CORE_DEBUG is
    generic (
        -- Number of PCIe endpoints
        PCIE_ENDPOINTS   : natural := 1;

        DBG_CRDT_PH_W    : natural := 12;
        DBG_CRDT_NPH_W   : natural := 12;
        DBG_CRDT_PD_W    : natural := 16;
        DBG_CRDT_NPD_W   : natural := 16;
        -- Enable debug probes
        DBG_ENABLE       : boolean := False;
        -- MI width - for access to debugging probes
        MI_WIDTH         : natural := 32;
        -- FPGA device
        DEVICE           : string  := "STRATIX10"
    );
    port (
        -- =====================================================================
        -- User PCIe clock and reset
        -- =====================================================================
        PCIE_CLK             : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        PCIE_RESET           : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        -- =====================================================================
        -- Input signals for debug probes
        -- =====================================================================
        DBG_UP_SRC_RDY       : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        DBG_UP_DST_RDY       : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        DBG_DW_SRC_RDY       : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        DBG_DW_DST_RDY       : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        DBG_CREDITS_PH       : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_CRDT_PH_W-1 downto 0);
        DBG_CREDITS_NPH      : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_CRDT_NPH_W-1 downto 0);
        DBG_CREDITS_PD       : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_CRDT_PD_W-1 downto 0);
        DBG_CREDITS_NPD      : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_CRDT_NPD_W-1 downto 0);

        DBG_CREDITS_PH_VLD   : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        DBG_CREDITS_NPH_VLD  : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        DBG_CREDITS_PD_VLD   : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        DBG_CREDITS_NPD_VLD  : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        -- =====================================================================
        -- MI interface (for debugging)
        -- =====================================================================
        MI_CLK               : in  std_logic;
        MI_RESET             : in  std_logic;
        MI_ADDR              : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_DWR               : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_BE                : in  std_logic_vector(MI_WIDTH/8-1 downto 0);
        MI_RD                : in  std_logic;
        MI_WR                : in  std_logic;
        MI_DRD               : out std_logic_vector(MI_WIDTH-1 downto 0);
        MI_ARDY              : out std_logic;
        MI_DRDY              : out std_logic
    );
end entity;

architecture FULL of PCIE_CORE_DEBUG is

    -- Number of watched signals.
    constant DBG_EVENT_SIGNALS       : natural := 4;
    -- Number of ranges (watched events) per each signal.
    -- Currently, there are 4 ranges for each of the signals.
    constant DBG_EVENT_RANGES        : i_array_t(DBG_EVENT_SIGNALS-1 downto 0) := (others => 4);
    -- Total number of watched events (all ranges for all signals).
    constant DBG_EVENTS              : natural := sum(DBG_EVENT_RANGES);
    -- Address offset for each Event Counter.
    constant DBG_EVENT_OFFSET        : natural := 16#10#;
    constant DBG_MAX_INTERVAL_CYCLES : natural := 2**24-1;
    constant DBG_MAX_INTERVALS       : natural := 1024;
    constant DBG_MI_INTERVAL_ADDR    : std_logic_vector(MI_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(0, MI_WIDTH));
    constant DBG_MI_EVENTS_ADDR      : std_logic_vector(MI_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(4, MI_WIDTH));
    constant DBG_MI_CAPTURE_EN_ADDR  : std_logic_vector(MI_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(8, MI_WIDTH));
    constant DBG_MI_CAPTURE_RD_ADDR  : std_logic_vector(MI_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(12, MI_WIDTH));
    constant DBG_MI_ADDR_MASK        : std_logic_vector(MI_WIDTH-1 downto 0) := (3 downto 2 => '1', others => '0');
    -- Number of Streaming Debug Probes per each PCIe Endpoint.
    constant DBG_PROBES              : natural := 2;
    -- Address offset for each Streaming Debug Probe.
    constant DBG_PROBE_OFFSET        : natural := 16#40#;
    -- Address offset of all Debug Probes per Endpoint.
    constant DBG_PROBES_OFFSET       : natural := DBG_PROBES*DBG_PROBE_OFFSET;
    -- Array of names (4-letter IDs) of Streaming Debug Probes
    -- This constant contains just the names of Probes of a single Streaming Debug Master.
    -- 2 Probes for 1x16 mode (there are 2 Avalon streams for one Endpoint).
    constant DBG_PROBE_STR           : string := "PAUPPADW"; -- (PAUP = PCIe AvST UP, PADW = PCIe AvST DOWN)
    -- Address offset for each Endpoint (containing the Debug Probes and Event Counters).
    constant ENDPT_OFFSET            : natural := DBG_PROBES*DBG_PROBE_OFFSET + DBG_EVENTS*DBG_EVENT_OFFSET;

    -- Address bases for Endpoints
    function mi_addr_base_endpts_f return slv_array_t is
        variable mi_addr_base : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    begin
        for pe in 0 to PCIE_ENDPOINTS-1 loop
            mi_addr_base(pe) := std_logic_vector(to_unsigned(pe*ENDPT_OFFSET, MI_WIDTH));
        end loop;
        return mi_addr_base;
    end function;

    -- Address bases for all Debug Probes and Event Counters in a single Endpoint
    function mi_addr_base_dbg_f return slv_array_t is
        variable mi_addr_base : slv_array_t(1+DBG_EVENTS-1 downto 0)(MI_WIDTH-1 downto 0);
    begin
        mi_addr_base(0) := (others => '0');
        for e in 0 to DBG_EVENTS-1 loop
            mi_addr_base(e+1) := std_logic_vector(to_unsigned(DBG_PROBES_OFFSET + e*DBG_EVENT_OFFSET, MI_WIDTH));
        end loop;
        return mi_addr_base;
    end function;

    --==============================================================================================
    -- Other debug signals
    --==============================================================================================
    signal mi_split_dwr         : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_addr        : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_be          : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH/8-1 downto 0);
    signal mi_split_rd          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_split_wr          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_split_ardy        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_split_drd         : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_drdy        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal mi_sync_dwr          : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_sync_addr         : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_sync_be           : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH/8-1 downto 0);
    signal mi_sync_rd           : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_sync_wr           : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_sync_ardy         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_sync_drd          : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_sync_drdy         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal mi_split_dbg_dwr     : slv_array_2d_t(PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_dbg_addr    : slv_array_2d_t(PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_dbg_be      : slv_array_2d_t(PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0)(MI_WIDTH/8-1 downto 0);
    signal mi_split_dbg_rd      : slv_array_t   (PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0);
    signal mi_split_dbg_wr      : slv_array_t   (PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0);
    signal mi_split_dbg_ardy    : slv_array_t   (PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0);
    signal mi_split_dbg_drd     : slv_array_2d_t(PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_dbg_drdy    : slv_array_t   (PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0);

    signal dp_out_src_rdy       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_PROBES-1 downto 0);
    signal dp_out_dst_rdy       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_PROBES-1 downto 0);

    -- Watched signals:
    -- 4 signals, each with 4 ranges => 4 bits for each watched signal
    -- Any changes and addition of other signals must be also reflected in constants (DBG_EVENT_SIGNALS, DBG_EVENT_RANGES)
    signal eve_ph               : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_pd               : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_nph              : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_npd              : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);

    signal eve_ph_reg           : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_pd_reg           : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_nph_reg          : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_npd_reg          : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);

    signal eve_all_reg          : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_EVENTS-1 downto 0);

begin

    -- =========================================================================
    --  DEBUG logic
    -- =========================================================================

    debug_g : if DBG_ENABLE generate

        mi_splitter_endpts_i : entity work.MI_SPLITTER_PLUS_GEN
        generic map (
            ADDR_WIDTH => MI_WIDTH,
            DATA_WIDTH => MI_WIDTH,
            PORTS      => PCIE_ENDPOINTS,
            ADDR_BASE  => mi_addr_base_endpts_f,
            PIPE_OUT   => (others => false),
            DEVICE     => DEVICE
        )
        port map (
            CLK     => MI_CLK,
            RESET   => MI_RESET,

            RX_DWR  => MI_DWR,
            RX_ADDR => MI_ADDR,
            RX_BE   => MI_BE,
            RX_RD   => MI_RD,
            RX_WR   => MI_WR,
            RX_ARDY => MI_ARDY,
            RX_DRD  => MI_DRD,
            RX_DRDY => MI_DRDY,

            TX_DWR  => mi_split_dwr,
            TX_ADDR => mi_split_addr,
            TX_BE   => mi_split_be,
            TX_RD   => mi_split_rd,
            TX_WR   => mi_split_wr,
            TX_ARDY => mi_split_ardy,
            TX_DRD  => mi_split_drd,
            TX_DRDY => mi_split_drdy
        );

        pcie_endpoints_dbg_g : for pe in 0 to PCIE_ENDPOINTS-1 generate

            -- ----------
            --  MI Async
            -- ----------
            mi_async_i : entity work.MI_ASYNC
            generic map (
                DEVICE => DEVICE
            )
            port map (
                CLK_M     => MI_CLK,
                RESET_M   => MI_RESET,
                MI_M_DWR  => mi_split_dwr (pe),
                MI_M_ADDR => mi_split_addr(pe),
                MI_M_RD   => mi_split_rd  (pe),
                MI_M_WR   => mi_split_wr  (pe),
                MI_M_BE   => mi_split_be  (pe),
                MI_M_DRD  => mi_split_drd (pe),
                MI_M_ARDY => mi_split_ardy(pe),
                MI_M_DRDY => mi_split_drdy(pe),

                CLK_S     => PCIE_CLK     (pe),
                RESET_S   => PCIE_RESET   (pe),
                MI_S_DWR  => mi_sync_dwr  (pe),
                MI_S_ADDR => mi_sync_addr (pe),
                MI_S_RD   => mi_sync_rd   (pe),
                MI_S_WR   => mi_sync_wr   (pe),
                MI_S_BE   => mi_sync_be   (pe),
                MI_S_DRD  => mi_sync_drd  (pe),
                MI_S_ARDY => mi_sync_ardy (pe),
                MI_S_DRDY => mi_sync_drdy (pe)
            );

            -- ----------------------------------------------------
            --  MI Splitter for all MI interfaces in each Endpoint
            -- ----------------------------------------------------
            mi_splitter_debug_i : entity work.MI_SPLITTER_PLUS_GEN
            generic map (
                ADDR_WIDTH => MI_WIDTH,
                DATA_WIDTH => MI_WIDTH,
                PORTS      => 1+DBG_EVENTS,
                ADDR_BASE  => mi_addr_base_dbg_f,
                PIPE_OUT   => (others => true),
                DEVICE     => DEVICE
            )
            port map (
                CLK     => PCIE_CLK         (pe),
                RESET   => PCIE_RESET       (pe),

                RX_DWR  => mi_sync_dwr      (pe),
                RX_ADDR => mi_sync_addr     (pe),
                RX_BE   => mi_sync_be       (pe),
                RX_RD   => mi_sync_rd       (pe),
                RX_WR   => mi_sync_wr       (pe),
                RX_ARDY => mi_sync_ardy     (pe),
                RX_DRD  => mi_sync_drd      (pe),
                RX_DRDY => mi_sync_drdy     (pe),

                TX_DWR  => mi_split_dbg_dwr (pe),
                TX_ADDR => mi_split_dbg_addr(pe),
                TX_BE   => mi_split_dbg_be  (pe),
                TX_RD   => mi_split_dbg_rd  (pe),
                TX_WR   => mi_split_dbg_wr  (pe),
                TX_ARDY => mi_split_dbg_ardy(pe),
                TX_DRD  => mi_split_dbg_drd (pe),
                TX_DRDY => mi_split_dbg_drdy(pe)
            );

            -- -----------------------------------------------
            --  Streaming Debug Master for each PCIe Endpoint
            -- -----------------------------------------------
            debug_master_i : entity work.STREAMING_DEBUG_MASTER
            generic map (
                CONNECTED_PROBES   => DBG_PROBES,
                REGIONS            => 1,
                DEBUG_ENABLED      => true,
                PROBE_ENABLED      => (1 to DBG_PROBES => 'E'),
                COUNTER_WORD       => (1 to DBG_PROBES => 'E'),
                COUNTER_WAIT       => (1 to DBG_PROBES => 'E'),
                COUNTER_DST_HOLD   => (1 to DBG_PROBES => 'E'),
                COUNTER_SRC_HOLD   => (1 to DBG_PROBES => 'E'),
                COUNTER_SOP        => (1 to DBG_PROBES => 'D'), -- disabled
                COUNTER_EOP        => (1 to DBG_PROBES => 'D'), -- disabled
                BUS_CONTROL        => (1 to DBG_PROBES => 'D'), -- disabled
                PROBE_NAMES        => DBG_PROBE_STR,
                DEBUG_REG          => true
            )
            port map (
                CLK           => PCIE_CLK         (pe),
                RESET         => PCIE_RESET       (pe),

                MI_DWR        => mi_split_dbg_dwr (pe)(0),
                MI_ADDR       => mi_split_dbg_addr(pe)(0),
                MI_RD         => mi_split_dbg_rd  (pe)(0),
                MI_WR         => mi_split_dbg_wr  (pe)(0),
                MI_BE         => mi_split_dbg_be  (pe)(0),
                MI_DRD        => mi_split_dbg_drd (pe)(0),
                MI_ARDY       => mi_split_dbg_ardy(pe)(0),
                MI_DRDY       => mi_split_dbg_drdy(pe)(0),

                DEBUG_BLOCK   => open,
                DEBUG_DROP    => open,
                DEBUG_SOP     => (others => '0'),
                DEBUG_EOP     => (others => '0'),
                DEBUG_SRC_RDY => dp_out_src_rdy   (pe),
                DEBUG_DST_RDY => dp_out_dst_rdy   (pe)
            );

            up_debug_probe_i : entity work.STREAMING_DEBUG_PROBE_MFB
            generic map (
                REGIONS => 1
            )
            port map (
                RX_SOF         => (others => '0'),
                RX_EOF         => (others => '0'),
                RX_SRC_RDY     => DBG_UP_SRC_RDY(pe),
                RX_DST_RDY     => open,

                TX_SOF         => open,
                TX_EOF         => open,
                TX_SRC_RDY     => open,
                TX_DST_RDY     => DBG_UP_DST_RDY(pe),

                DEBUG_BLOCK    => '0',
                DEBUG_DROP     => '0',
                DEBUG_SOF      => open,
                DEBUG_EOF      => open,
                DEBUG_SRC_RDY  => dp_out_src_rdy(pe)(0),
                DEBUG_DST_RDY  => dp_out_dst_rdy(pe)(0)
            );

            down_debug_probe_i : entity work.STREAMING_DEBUG_PROBE_MFB
            generic map (
                REGIONS => 1
            )
            port map (
                RX_SOF         => (others => '0'),
                RX_EOF         => (others => '0'),
                RX_SRC_RDY     => DBG_DW_SRC_RDY(pe),
                RX_DST_RDY     => open,

                TX_SOF         => open,
                TX_EOF         => open,
                TX_SRC_RDY     => open,
                TX_DST_RDY     => DBG_DW_DST_RDY(pe),

                DEBUG_BLOCK    => '0',
                DEBUG_DROP     => '0',
                DEBUG_SOF      => open,
                DEBUG_EOF      => open,
                DEBUG_SRC_RDY  => dp_out_src_rdy(pe)(1),
                DEBUG_DST_RDY  => dp_out_dst_rdy(pe)(1)
            );

            -- ----------------
            --  Event Counters
            -- ----------------
            eve_cnt_g : for de in 0 to DBG_EVENTS-1 generate
                eve_cnt_i : entity work.EVENT_COUNTER_MI_WRAPPER
                generic map (
                    MAX_INTERVAL_CYCLES   => DBG_MAX_INTERVAL_CYCLES,
                    MAX_CONCURRENT_EVENTS => 1,
                    CAPTURE_EN            => True,
                    CAPTURE_FIFO_ITEMS    => DBG_MAX_INTERVALS,
                    MI_WIDTH              => MI_WIDTH,
                    MI_INTERVAL_ADDR      => DBG_MI_INTERVAL_ADDR,
                    MI_EVENTS_ADDR        => DBG_MI_EVENTS_ADDR,
                    MI_CPT_EN_ADDR        => DBG_MI_CAPTURE_EN_ADDR,
                    MI_CPT_RD_ADDR        => DBG_MI_CAPTURE_RD_ADDR,
                    MI_ADDR_MASK          => DBG_MI_ADDR_MASK
                )
                port map (
                    CLK       => PCIE_CLK         (pe),
                    RESET     => PCIE_RESET       (pe),

                    MI_DWR    => mi_split_dbg_dwr (pe)(de+1),
                    MI_ADDR   => mi_split_dbg_addr(pe)(de+1),
                    MI_RD     => mi_split_dbg_rd  (pe)(de+1),
                    MI_WR     => mi_split_dbg_wr  (pe)(de+1),
                    MI_ARDY   => mi_split_dbg_ardy(pe)(de+1),
                    MI_DRDY   => mi_split_dbg_drdy(pe)(de+1),
                    MI_DRD    => mi_split_dbg_drd (pe)(de+1),

                    EVENT_CNT => (others => '1'),
                    EVENT_VLD => eve_all_reg      (pe)(de)
                );
            end generate;

            -- The connection of the four watched signals
            eve_all_reg(pe)(1*4-1 downto 0*4) <= eve_ph_reg (pe); -- Posted Headers
            eve_all_reg(pe)(2*4-1 downto 1*4) <= eve_pd_reg (pe); -- Posted Data
            eve_all_reg(pe)(3*4-1 downto 2*4) <= eve_nph_reg(pe); -- Non-Posted Headers
            eve_all_reg(pe)(4*4-1 downto 3*4) <= eve_npd_reg(pe); -- Non-Posted Data

            -- Posted Headers
            process (PCIE_CLK(pe))
            begin
                if (rising_edge(PCIE_CLK(pe))) then
                    eve_ph(pe)(0)  <= DBG_CREDITS_PH_VLD(pe) when (unsigned(DBG_CREDITS_PH(pe)) >= 0 ) and (unsigned(DBG_CREDITS_PH(pe)) <= 7  ) else '0'; -- 0-7    available Descriptors
                    eve_ph(pe)(1)  <= DBG_CREDITS_PH_VLD(pe) when (unsigned(DBG_CREDITS_PH(pe)) >= 8 ) and (unsigned(DBG_CREDITS_PH(pe)) <= 31 ) else '0'; -- 8-31   available Descriptors
                    eve_ph(pe)(2)  <= DBG_CREDITS_PH_VLD(pe) when (unsigned(DBG_CREDITS_PH(pe)) >= 32) and (unsigned(DBG_CREDITS_PH(pe)) <= 127) else '0'; -- 32-127 available Descriptors
                    eve_ph(pe)(3)  <= DBG_CREDITS_PH_VLD(pe) when (unsigned(DBG_CREDITS_PH(pe)) >= 128)                                          else '0'; -- 127+   available Descriptors
                    eve_ph_reg(pe) <= eve_ph(pe);
                end if;
            end process;

            -- Non-Posted Headers
            process (PCIE_CLK(pe))
            begin
                if (rising_edge(PCIE_CLK(pe))) then
                    eve_nph(pe)(0)  <= DBG_CREDITS_NPH_VLD(pe) when (unsigned(DBG_CREDITS_NPH(pe)) >= 0 ) and (unsigned(DBG_CREDITS_NPH(pe)) <= 7  ) else '0'; -- 0-7    available Descriptors
                    eve_nph(pe)(1)  <= DBG_CREDITS_NPH_VLD(pe) when (unsigned(DBG_CREDITS_NPH(pe)) >= 8 ) and (unsigned(DBG_CREDITS_NPH(pe)) <= 31 ) else '0'; -- 8-31   available Descriptors
                    eve_nph(pe)(2)  <= DBG_CREDITS_NPH_VLD(pe) when (unsigned(DBG_CREDITS_NPH(pe)) >= 32) and (unsigned(DBG_CREDITS_NPH(pe)) <= 127) else '0'; -- 32-127 available Descriptors
                    eve_nph(pe)(3)  <= DBG_CREDITS_NPH_VLD(pe) when (unsigned(DBG_CREDITS_NPH(pe)) >= 128)                                           else '0'; -- 127+   available Descriptors                                                    -- 127+   available Descriptors
                    eve_nph_reg(pe) <= eve_nph(pe);
                end if;
            end process;

            -- Posted Data
            process (PCIE_CLK(pe))
            begin
                if (rising_edge(PCIE_CLK(pe))) then
                    eve_pd(pe)(0)  <= DBG_CREDITS_PD_VLD(pe) when (unsigned(DBG_CREDITS_PD(pe)) >= 0 ) and (unsigned(DBG_CREDITS_PD(pe)) <= 7  ) else '0'; -- 0-7    available Descriptors
                    eve_pd(pe)(1)  <= DBG_CREDITS_PD_VLD(pe) when (unsigned(DBG_CREDITS_PD(pe)) >= 8 ) and (unsigned(DBG_CREDITS_PD(pe)) <= 31 ) else '0'; -- 8-31   available Descriptors
                    eve_pd(pe)(2)  <= DBG_CREDITS_PD_VLD(pe) when (unsigned(DBG_CREDITS_PD(pe)) >= 32) and (unsigned(DBG_CREDITS_PD(pe)) <= 127) else '0'; -- 32-127 available Descriptors
                    eve_pd(pe)(3)  <= DBG_CREDITS_PD_VLD(pe) when (unsigned(DBG_CREDITS_PD(pe)) >= 128)                                          else '0'; -- 127+   available Descriptors                                                    -- 127+   available Descriptors
                    eve_pd_reg(pe) <= eve_pd(pe);
                end if;
            end process;

            -- Non-Posted Data
            process (PCIE_CLK(pe))
            begin
                if (rising_edge(PCIE_CLK(pe))) then
                    eve_npd(pe)(0)  <= DBG_CREDITS_NPD_VLD(pe) when (unsigned(DBG_CREDITS_NPD(pe)) >= 0 ) and (unsigned(DBG_CREDITS_NPD(pe)) <= 7  ) else '0'; -- 0-7    available Descriptors
                    eve_npd(pe)(1)  <= DBG_CREDITS_NPD_VLD(pe) when (unsigned(DBG_CREDITS_NPD(pe)) >= 8 ) and (unsigned(DBG_CREDITS_NPD(pe)) <= 31 ) else '0'; -- 8-31   available Descriptors
                    eve_npd(pe)(2)  <= DBG_CREDITS_NPD_VLD(pe) when (unsigned(DBG_CREDITS_NPD(pe)) >= 32) and (unsigned(DBG_CREDITS_NPD(pe)) <= 127) else '0'; -- 32-127 available Descriptors
                    eve_npd(pe)(3)  <= DBG_CREDITS_NPD_VLD(pe) when (unsigned(DBG_CREDITS_NPD(pe)) >= 128)                                           else '0'; -- 127+   available Descriptors                                                   -- 127+   available Descriptors
                    eve_npd_reg(pe) <= eve_npd(pe);
                end if;
            end process;

        end generate;

    else generate
        MI_DRD  <= (others => '0');
        MI_ARDY <= MI_RD or MI_WR;
        MI_DRDY <= MI_RD;
    end generate;

end architecture;
