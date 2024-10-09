-- network_mod_core_etile.vhd: core of the Network module with Ethernet E-TILE(s).
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

-- NOTE: generated 25g4 and 10g4 IPs have incorrectly generated generic settings: rx and tx_max_frame_size, rx and tx_vlan_detection
--       original values: rx_max_frame_size = tx_max_frame_size = 1518 , rx_vlan_detection = tx_vlan_detection = "disable"
--       required values: rx_max_frame_size = tx_max_frame_size = 16383, rx_vlan_detection = tx_vlan_detection = "enable"

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;


-- Thi E-Tile design also contains extra demo/testing logic for Timestamp Limiting (see the Timestamp Limiter unit).
-- The logic is enabled by the :vhdl:genconstant:`TS_DEMO_EN <network_mod_core.network_mod_core>` generic.
--
-- .. Warning::
--      The Demo/Testing logic works only for a single-channel (and single-Region) designs with E-Tile (Intel)!
--
-- **MI address space**
--
-- Is allocated after the address space of the MGMT unit

architecture ETILE of NETWORK_MOD_CORE is

    -- =========================================================================
    --                        COMPONENTS - E_TILE
    -- =========================================================================
    -- 100g1
    component etile_eth_1x100g is
    generic (
        am_encoding40g_0              : integer := 9467463;
        am_encoding40g_1              : integer := 15779046;
        am_encoding40g_2              : integer := 12936603;
        am_encoding40g_3              : integer := 10647869;
        enforce_max_frame_size        : string  := "disable";
        flow_control                  : string  := "both_no_xoff";
        flow_control_holdoff_mode     : string  := "uniform";
        forward_rx_pause_requests     : string  := "disable";
        hi_ber_monitor                : string  := "enable";
        holdoff_quanta                : integer := 65535;
        ipg_removed_per_am_period     : integer := 20;
        link_fault_mode               : string  := "lf_bidir";
        pause_quanta                  : integer := 65535;
        pfc_holdoff_quanta_0          : integer := 65535;
        pfc_holdoff_quanta_1          : integer := 65535;
        pfc_holdoff_quanta_2          : integer := 65535;
        pfc_holdoff_quanta_3          : integer := 65535;
        pfc_holdoff_quanta_4          : integer := 65535;
        pfc_holdoff_quanta_5          : integer := 65535;
        pfc_holdoff_quanta_6          : integer := 65535;
        pfc_holdoff_quanta_7          : integer := 65535;
        pfc_pause_quanta_0            : integer := 65535;
        pfc_pause_quanta_1            : integer := 65535;
        pfc_pause_quanta_2            : integer := 65535;
        pfc_pause_quanta_3            : integer := 65535;
        pfc_pause_quanta_4            : integer := 65535;
        pfc_pause_quanta_5            : integer := 65535;
        pfc_pause_quanta_6            : integer := 65535;
        pfc_pause_quanta_7            : integer := 65535;
        remove_pads                   : string  := "disable";
        rx_length_checking            : string  := "disable";
        rx_max_frame_size             : integer := 16383;
        rx_pause_daddr                : string  := "17483607389996";
        rx_pcs_max_skew               : integer := 47;
        rx_vlan_detection             : string  := "disable";
        rxcrc_covers_preamble         : string  := "disable";
        sim_mode                      : string  := "enable";
        source_address_insertion      : string  := "disable";
        strict_preamble_checking      : string  := "disable";
        strict_sfd_checking           : string  := "disable";
        tx_ipg_size                   : string  := "ipg_12";
        tx_max_frame_size             : integer := 16383;
        tx_pause_daddr                : string  := "1652522221569";
        tx_pause_saddr                : string  := "247393538562781";
        tx_pld_fifo_almost_full_level : integer := 16;
        tx_vlan_detection             : string  := "disable";
        txcrc_covers_preamble         : string  := "disable";
        txmac_saddr                   : string  := "73588229205";
        uniform_holdoff_quanta        : integer := 51090;
        flow_control_sl_0             : string  := "both_no_xoff"
    );
    port (
        i_stats_snapshot              : in  std_logic                      := 'X';             -- i_stats_snapshot
        o_cdr_lock                    : out std_logic_vector(0 downto 0);                      -- o_cdr_lock
        o_tx_pll_locked               : out std_logic_vector(0 downto 0);                      -- o_tx_pll_locked
        i_eth_reconfig_addr           : in  std_logic_vector(20 downto 0)  := (others => 'X'); -- i_eth_reconfig_addr
        i_eth_reconfig_read           : in  std_logic                      := 'X';             -- i_eth_reconfig_read
        i_eth_reconfig_write          : in  std_logic                      := 'X';             -- i_eth_reconfig_write
        o_eth_reconfig_readdata       : out std_logic_vector(31 downto 0);                     -- o_eth_reconfig_readdata
        o_eth_reconfig_readdata_valid : out std_logic;                                         -- o_eth_reconfig_readdata_valid
        i_eth_reconfig_writedata      : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- i_eth_reconfig_writedata
        o_eth_reconfig_waitrequest    : out std_logic;                                         -- o_eth_reconfig_waitrequest
        i_rsfec_reconfig_addr         : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- i_rsfec_reconfig_addr
        i_rsfec_reconfig_read         : in  std_logic                      := 'X';             -- i_rsfec_reconfig_read
        i_rsfec_reconfig_write        : in  std_logic                      := 'X';             -- i_rsfec_reconfig_write
        o_rsfec_reconfig_readdata     : out std_logic_vector(7 downto 0);                      -- o_rsfec_reconfig_readdata
        i_rsfec_reconfig_writedata    : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- i_rsfec_reconfig_writedata
        o_rsfec_reconfig_waitrequest  : out std_logic;                                         -- o_rsfec_reconfig_waitrequest
        o_tx_lanes_stable             : out std_logic;                                         -- o_tx_lanes_stable
        o_rx_pcs_ready                : out std_logic;                                         -- o_rx_pcs_ready
        o_ehip_ready                  : out std_logic;                                         -- o_ehip_ready
        o_rx_block_lock               : out std_logic;                                         -- o_rx_block_lock
        o_rx_am_lock                  : out std_logic;                                         -- o_rx_am_lock
        o_rx_hi_ber                   : out std_logic;                                         -- o_rx_hi_ber
        o_local_fault_status          : out std_logic;                                         -- o_local_fault_status
        o_remote_fault_status         : out std_logic;                                         -- o_remote_fault_status
        i_clk_ref                     : in  std_logic_vector(0 downto 0)   := (others => 'X'); -- i_clk_ref
        i_clk_tx                      : in  std_logic                      := 'X';             -- clk
        i_clk_rx                      : in  std_logic                      := 'X';             -- clk
        o_clk_pll_div64               : out std_logic_vector(0 downto 0);                      -- o_clk_pll_div64
        o_clk_pll_div66               : out std_logic_vector(0 downto 0);                      -- o_clk_pll_div66
        o_clk_rec_div64               : out std_logic_vector(0 downto 0);                      -- o_clk_rec_div64
        o_clk_rec_div66               : out std_logic_vector(0 downto 0);                      -- o_clk_rec_div66
        i_csr_rst_n                   : in  std_logic                      := 'X';             -- reset
        i_tx_rst_n                    : in  std_logic                      := 'X';             -- i_tx_rst_n
        i_rx_rst_n                    : in  std_logic                      := 'X';             -- i_rx_rst_n
        o_tx_serial                   : out std_logic_vector(3 downto 0);                      -- o_tx_serial
        i_rx_serial                   : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_rx_serial
        o_tx_serial_n                 : out std_logic_vector(3 downto 0);                      -- o_tx_serial_n
        i_rx_serial_n                 : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_rx_serial_n
        i_reconfig_clk                : in  std_logic                      := 'X';             -- clk
        i_reconfig_reset              : in  std_logic                      := 'X';             -- i_reconfig_reset
        i_xcvr_reconfig_address       : in  std_logic_vector(75 downto 0)  := (others => 'X'); -- i_xcvr_reconfig_address
        i_xcvr_reconfig_read          : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_xcvr_reconfig_read
        i_xcvr_reconfig_write         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_xcvr_reconfig_write
        o_xcvr_reconfig_readdata      : out std_logic_vector(31 downto 0);                     -- o_xcvr_reconfig_readdata
        i_xcvr_reconfig_writedata     : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- i_xcvr_reconfig_writedata
        o_xcvr_reconfig_waitrequest   : out std_logic_vector(3 downto 0);                      -- o_xcvr_reconfig_waitrequest
        o_tx_ready                    : out std_logic;                                         -- o_tx_ready
        i_tx_valid                    : in  std_logic                      := 'X';             -- i_tx_valid
        i_tx_data                     : in  std_logic_vector(511 downto 0) := (others => 'X'); -- i_tx_data
        i_tx_error                    : in  std_logic                      := 'X';             -- i_tx_error
        i_tx_startofpacket            : in  std_logic                      := 'X';             -- i_tx_startofpacket
        i_tx_endofpacket              : in  std_logic                      := 'X';             -- i_tx_endofpacket
        i_tx_empty                    : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- i_tx_empty
        i_tx_skip_crc                 : in  std_logic                      := 'X';             -- i_tx_skip_crc
        o_rx_valid                    : out std_logic;                                         -- o_rx_valid
        o_rx_data                     : out std_logic_vector(511 downto 0);                    -- o_rx_data
        o_rx_startofpacket            : out std_logic;                                         -- o_rx_startofpacket
        o_rx_endofpacket              : out std_logic;                                         -- o_rx_endofpacket
        o_rx_empty                    : out std_logic_vector(5 downto 0);                      -- o_rx_empty
        o_rx_error                    : out std_logic_vector(5 downto 0);                      -- o_rx_error
        o_rxstatus_data               : out std_logic_vector(39 downto 0);                     -- o_rxstatus_data
        o_rxstatus_valid              : out std_logic;                                         -- o_rxstatus_valid
        i_tx_pfc                      : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- i_tx_pfc
        o_rx_pfc                      : out std_logic_vector(7 downto 0);                      -- o_rx_pfc
        i_tx_pause                    : in  std_logic                      := 'X';             -- i_tx_pause
        o_rx_pause                    : out std_logic                                          -- o_rx_pause
    );
    end component etile_eth_1x100g;

    -- 25g4
    component etile_eth_4x25g is
    generic (
        am_encoding40g_0              : integer := 9467463;
        am_encoding40g_1              : integer := 15779046;
        am_encoding40g_2              : integer := 12936603;
        am_encoding40g_3              : integer := 10647869;
        enforce_max_frame_size        : string  := "disable";
        flow_control                  : string  := "both_no_xoff";
        flow_control_holdoff_mode     : string  := "uniform";
        forward_rx_pause_requests     : string  := "disable";
        hi_ber_monitor                : string  := "enable";
        holdoff_quanta                : integer := 65535;
        ipg_removed_per_am_period     : integer := 20;
        link_fault_mode               : string  := "lf_bidir";
        pause_quanta                  : integer := 65535;
        pfc_holdoff_quanta_0          : integer := 32768;
        pfc_holdoff_quanta_1          : integer := 32768;
        pfc_holdoff_quanta_2          : integer := 32768;
        pfc_holdoff_quanta_3          : integer := 32768;
        pfc_holdoff_quanta_4          : integer := 32768;
        pfc_holdoff_quanta_5          : integer := 32768;
        pfc_holdoff_quanta_6          : integer := 32768;
        pfc_holdoff_quanta_7          : integer := 32768;
        pfc_pause_quanta_0            : integer := 65535;
        pfc_pause_quanta_1            : integer := 65535;
        pfc_pause_quanta_2            : integer := 65535;
        pfc_pause_quanta_3            : integer := 65535;
        pfc_pause_quanta_4            : integer := 65535;
        pfc_pause_quanta_5            : integer := 65535;
        pfc_pause_quanta_6            : integer := 65535;
        pfc_pause_quanta_7            : integer := 65535;
        remove_pads                   : string  := "disable";
        rx_length_checking            : string  := "disable";
        rx_max_frame_size             : integer := 16383;
        rx_pause_daddr                : string  := "17483607389996";
        rx_pcs_max_skew               : integer := 47;
        rx_vlan_detection             : string  := "disable";
        rxcrc_covers_preamble         : string  := "disable";
        sim_mode                      : string  := "enable";
        source_address_insertion      : string  := "disable";
        strict_preamble_checking      : string  := "disable";
        strict_sfd_checking           : string  := "disable";
        tx_ipg_size                   : string  := "ipg_12";
        tx_max_frame_size             : integer := 16383;
        tx_pause_daddr                : string  := "1652522221569";
        tx_pause_saddr                : string  := "73588229205";
        tx_pld_fifo_almost_full_level : integer := 16;
        tx_vlan_detection             : string  := "disable";
        txcrc_covers_preamble         : string  := "disable";
        txmac_saddr                   : string  := "73588229205";
        uniform_holdoff_quanta        : integer := 51090;
        flow_control_sl_0             : string  := "both_no_xoff"
    );
    port (
        o_cdr_lock                       : out std_logic_vector(3 downto 0);                      -- o_cdr_lock
        o_tx_pll_locked                  : out std_logic_vector(3 downto 0);                      -- o_tx_pll_locked
        i_rsfec_reconfig_addr            : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- i_rsfec_reconfig_addr
        i_rsfec_reconfig_read            : in  std_logic                      := 'X';             -- i_rsfec_reconfig_read
        i_rsfec_reconfig_write           : in  std_logic                      := 'X';             -- i_rsfec_reconfig_write
        o_rsfec_reconfig_readdata        : out std_logic_vector(7 downto 0);                      -- o_rsfec_reconfig_readdata
        i_rsfec_reconfig_writedata       : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- i_rsfec_reconfig_writedata
        o_rsfec_reconfig_waitrequest     : out std_logic;                                         -- o_rsfec_reconfig_waitrequest
        i_clk_ref                        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_clk_ref
        o_clk_pll_div64                  : out std_logic_vector(3 downto 0);                      -- o_clk_pll_div64
        o_clk_pll_div66                  : out std_logic_vector(3 downto 0);                      -- o_clk_pll_div66
        o_clk_rec_div64                  : out std_logic_vector(3 downto 0);                      -- o_clk_rec_div64
        o_clk_rec_div66                  : out std_logic_vector(3 downto 0);                      -- o_clk_rec_div66
        o_tx_serial                      : out std_logic_vector(3 downto 0);                      -- o_tx_serial
        i_rx_serial                      : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_rx_serial
        o_tx_serial_n                    : out std_logic_vector(3 downto 0);                      -- o_tx_serial_n
        i_rx_serial_n                    : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_rx_serial_n
        i_reconfig_clk                   : in  std_logic                      := 'X';             -- clk
        i_reconfig_reset                 : in  std_logic                      := 'X';             -- i_reconfig_reset
        i_xcvr_reconfig_address          : in  std_logic_vector(75 downto 0)  := (others => 'X'); -- i_xcvr_reconfig_address
        i_xcvr_reconfig_read             : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_xcvr_reconfig_read
        i_xcvr_reconfig_write            : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_xcvr_reconfig_write
        o_xcvr_reconfig_readdata         : out std_logic_vector(31 downto 0);                     -- o_xcvr_reconfig_readdata
        i_xcvr_reconfig_writedata        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- i_xcvr_reconfig_writedata
        o_xcvr_reconfig_waitrequest      : out std_logic_vector(3 downto 0);                      -- o_xcvr_reconfig_waitrequest
        i_sl_stats_snapshot              : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_stats_snapshot
        o_sl_rx_hi_ber                   : out std_logic_vector(3 downto 0);                      -- o_sl_rx_hi_ber
        i_sl_eth_reconfig_addr           : in  std_logic_vector(75 downto 0)  := (others => 'X'); -- i_sl_eth_reconfig_addr
        i_sl_eth_reconfig_read           : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_eth_reconfig_read
        i_sl_eth_reconfig_write          : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_eth_reconfig_write
        o_sl_eth_reconfig_readdata       : out std_logic_vector(127 downto 0);                    -- o_sl_eth_reconfig_readdata
        o_sl_eth_reconfig_readdata_valid : out std_logic_vector(3 downto 0);                      -- o_sl_eth_reconfig_readdata_valid
        i_sl_eth_reconfig_writedata      : in  std_logic_vector(127 downto 0) := (others => 'X'); -- i_sl_eth_reconfig_writedata
        o_sl_eth_reconfig_waitrequest    : out std_logic_vector(3 downto 0);                      -- o_sl_eth_reconfig_waitrequest
        o_sl_tx_lanes_stable             : out std_logic_vector(3 downto 0);                      -- o_sl_tx_lanes_stable
        o_sl_rx_pcs_ready                : out std_logic_vector(3 downto 0);                      -- o_sl_rx_pcs_ready
        o_sl_ehip_ready                  : out std_logic_vector(3 downto 0);                      -- o_sl_ehip_ready
        o_sl_rx_block_lock               : out std_logic_vector(3 downto 0);                      -- o_sl_rx_block_lock
        o_sl_local_fault_status          : out std_logic_vector(3 downto 0);                      -- o_sl_local_fault_status
        o_sl_remote_fault_status         : out std_logic_vector(3 downto 0);                      -- o_sl_remote_fault_status
        i_sl_clk_tx                      : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_clk_tx
        i_sl_clk_rx                      : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_clk_rx
        i_sl_csr_rst_n                   : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_csr_rst_n
        i_sl_tx_rst_n                    : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_rst_n
        i_sl_rx_rst_n                    : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_rx_rst_n
        o_sl_txfifo_pfull                : out std_logic_vector(3 downto 0);                      -- o_sl_txfifo_pfull
        o_sl_txfifo_pempty               : out std_logic_vector(3 downto 0);                      -- o_sl_txfifo_pempty
        o_sl_txfifo_overflow             : out std_logic_vector(3 downto 0);                      -- o_sl_txfifo_overflow
        o_sl_txfifo_underflow            : out std_logic_vector(3 downto 0);                      -- o_sl_txfifo_underflow
        o_sl_tx_ready                    : out std_logic_vector(3 downto 0);                      -- o_sl_tx_ready
        o_sl_rx_valid                    : out std_logic_vector(3 downto 0);                      -- o_sl_rx_valid
        i_sl_tx_valid                    : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_valid
        i_sl_tx_data                     : in  std_logic_vector(255 downto 0) := (others => 'X'); -- i_sl_tx_data
        o_sl_rx_data                     : out std_logic_vector(255 downto 0);                    -- o_sl_rx_data
        i_sl_tx_error                    : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_error
        i_sl_tx_startofpacket            : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_startofpacket
        i_sl_tx_endofpacket              : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_endofpacket
        i_sl_tx_empty                    : in  std_logic_vector(11 downto 0)  := (others => 'X'); -- i_sl_tx_empty
        i_sl_tx_skip_crc                 : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_skip_crc
        o_sl_rx_startofpacket            : out std_logic_vector(3 downto 0);                      -- o_sl_rx_startofpacket
        o_sl_rx_endofpacket              : out std_logic_vector(3 downto 0);                      -- o_sl_rx_endofpacket
        o_sl_rx_empty                    : out std_logic_vector(11 downto 0);                     -- o_sl_rx_empty
        o_sl_rx_error                    : out std_logic_vector(23 downto 0);                     -- o_sl_rx_error
        o_sl_rxstatus_data               : out std_logic_vector(159 downto 0);                    -- o_sl_rxstatus_data
        o_sl_rxstatus_valid              : out std_logic_vector(3 downto 0);                      -- o_sl_rxstatus_valid
        i_sl_tx_pfc                      : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- i_sl_tx_pfc
        o_sl_rx_pfc                      : out std_logic_vector(31 downto 0);                     -- o_sl_rx_pfc
        i_sl_tx_pause                    : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_pause
        o_sl_rx_pause                    : out std_logic_vector(3 downto 0)                       -- o_sl_rx_pause
    );
    end component etile_eth_4x25g;

    -- 10g4
    component etile_eth_4x10g is
    generic (
        am_encoding40g_0              : integer := 9467463;
        am_encoding40g_1              : integer := 15779046;
        am_encoding40g_2              : integer := 12936603;
        am_encoding40g_3              : integer := 10647869;
        enforce_max_frame_size        : string  := "disable";
        flow_control                  : string  := "both_no_xoff";
        flow_control_holdoff_mode     : string  := "per_queue";
        forward_rx_pause_requests     : string  := "disable";
        hi_ber_monitor                : string  := "enable";
        holdoff_quanta                : integer := 65535;
        ipg_removed_per_am_period     : integer := 20;
        link_fault_mode               : string  := "lf_bidir";
        pause_quanta                  : integer := 65535;
        pfc_holdoff_quanta_0          : integer := 32768;
        pfc_holdoff_quanta_1          : integer := 32768;
        pfc_holdoff_quanta_2          : integer := 32768;
        pfc_holdoff_quanta_3          : integer := 32768;
        pfc_holdoff_quanta_4          : integer := 32768;
        pfc_holdoff_quanta_5          : integer := 32768;
        pfc_holdoff_quanta_6          : integer := 32768;
        pfc_holdoff_quanta_7          : integer := 32768;
        pfc_pause_quanta_0            : integer := 65535;
        pfc_pause_quanta_1            : integer := 65535;
        pfc_pause_quanta_2            : integer := 65535;
        pfc_pause_quanta_3            : integer := 65535;
        pfc_pause_quanta_4            : integer := 65535;
        pfc_pause_quanta_5            : integer := 65535;
        pfc_pause_quanta_6            : integer := 65535;
        pfc_pause_quanta_7            : integer := 65535;
        remove_pads                   : string  := "disable";
        rx_length_checking            : string  := "enable";
        rx_max_frame_size             : integer := 16383;
        rx_pause_daddr                : string  := "1652522221569";
        rx_pcs_max_skew               : integer := 47;
        rx_vlan_detection             : string  := "disable";
        rxcrc_covers_preamble         : string  := "disable";
        sim_mode                      : string  := "enable";
        source_address_insertion      : string  := "disable";
        strict_preamble_checking      : string  := "disable";
        strict_sfd_checking           : string  := "disable";
        tx_ipg_size                   : string  := "ipg_12";
        tx_max_frame_size             : integer := 16383;
        tx_pause_daddr                : string  := "1652522221569";
        tx_pause_saddr                : string  := "73588229205";
        tx_pld_fifo_almost_full_level : integer := 16;
        tx_vlan_detection             : string  := "disable";
        txcrc_covers_preamble         : string  := "disable";
        txmac_saddr                   : string  := "73588229205";
        uniform_holdoff_quanta        : integer := 65535;
        flow_control_sl_0             : string  := "both_no_xoff"
    );
    port (
        o_cdr_lock                       : out std_logic_vector(3 downto 0);                      -- o_cdr_lock
        o_tx_pll_locked                  : out std_logic_vector(3 downto 0);                      -- o_tx_pll_locked
        i_clk_ref                        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_clk_ref
        o_clk_pll_div64                  : out std_logic_vector(3 downto 0);                      -- o_clk_pll_div64
        o_clk_pll_div66                  : out std_logic_vector(3 downto 0);                      -- o_clk_pll_div66
        o_clk_rec_div64                  : out std_logic_vector(3 downto 0);                      -- o_clk_rec_div64
        o_clk_rec_div66                  : out std_logic_vector(3 downto 0);                      -- o_clk_rec_div66
        o_tx_serial                      : out std_logic_vector(3 downto 0);                      -- o_tx_serial
        i_rx_serial                      : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_rx_serial
        o_tx_serial_n                    : out std_logic_vector(3 downto 0);                      -- o_tx_serial_n
        i_rx_serial_n                    : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_rx_serial_n
        i_reconfig_clk                   : in  std_logic                      := 'X';             -- clk
        i_reconfig_reset                 : in  std_logic                      := 'X';             -- i_reconfig_reset
        i_xcvr_reconfig_address          : in  std_logic_vector(75 downto 0)  := (others => 'X'); -- i_xcvr_reconfig_address
        i_xcvr_reconfig_read             : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_xcvr_reconfig_read
        i_xcvr_reconfig_write            : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_xcvr_reconfig_write
        o_xcvr_reconfig_readdata         : out std_logic_vector(31 downto 0);                     -- o_xcvr_reconfig_readdata
        i_xcvr_reconfig_writedata        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- i_xcvr_reconfig_writedata
        o_xcvr_reconfig_waitrequest      : out std_logic_vector(3 downto 0);                      -- o_xcvr_reconfig_waitrequest
        i_sl_stats_snapshot              : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_stats_snapshot
        o_sl_rx_hi_ber                   : out std_logic_vector(3 downto 0);                      -- o_sl_rx_hi_ber
        i_sl_eth_reconfig_addr           : in  std_logic_vector(75 downto 0)  := (others => 'X'); -- i_sl_eth_reconfig_addr
        i_sl_eth_reconfig_read           : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_eth_reconfig_read
        i_sl_eth_reconfig_write          : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_eth_reconfig_write
        o_sl_eth_reconfig_readdata       : out std_logic_vector(127 downto 0);                    -- o_sl_eth_reconfig_readdata
        o_sl_eth_reconfig_readdata_valid : out std_logic_vector(3 downto 0);                      -- o_sl_eth_reconfig_readdata_valid
        i_sl_eth_reconfig_writedata      : in  std_logic_vector(127 downto 0) := (others => 'X'); -- i_sl_eth_reconfig_writedata
        o_sl_eth_reconfig_waitrequest    : out std_logic_vector(3 downto 0);                      -- o_sl_eth_reconfig_waitrequest
        o_sl_tx_lanes_stable             : out std_logic_vector(3 downto 0);                      -- o_sl_tx_lanes_stable
        o_sl_rx_pcs_ready                : out std_logic_vector(3 downto 0);                      -- o_sl_rx_pcs_ready
        o_sl_ehip_ready                  : out std_logic_vector(3 downto 0);                      -- o_sl_ehip_ready
        o_sl_rx_block_lock               : out std_logic_vector(3 downto 0);                      -- o_sl_rx_block_lock
        o_sl_local_fault_status          : out std_logic_vector(3 downto 0);                      -- o_sl_local_fault_status
        o_sl_remote_fault_status         : out std_logic_vector(3 downto 0);                      -- o_sl_remote_fault_status
        i_sl_clk_tx                      : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_clk_tx
        i_sl_clk_rx                      : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_clk_rx
        i_sl_csr_rst_n                   : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_csr_rst_n
        i_sl_tx_rst_n                    : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_rst_n
        i_sl_rx_rst_n                    : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_rx_rst_n
        o_sl_txfifo_pfull                : out std_logic_vector(3 downto 0);                      -- o_sl_txfifo_pfull
        o_sl_txfifo_pempty               : out std_logic_vector(3 downto 0);                      -- o_sl_txfifo_pempty
        o_sl_txfifo_overflow             : out std_logic_vector(3 downto 0);                      -- o_sl_txfifo_overflow
        o_sl_txfifo_underflow            : out std_logic_vector(3 downto 0);                      -- o_sl_txfifo_underflow
        o_sl_tx_ready                    : out std_logic_vector(3 downto 0);                      -- o_sl_tx_ready
        o_sl_rx_valid                    : out std_logic_vector(3 downto 0);                      -- o_sl_rx_valid
        i_sl_tx_valid                    : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_valid
        i_sl_tx_data                     : in  std_logic_vector(255 downto 0) := (others => 'X'); -- i_sl_tx_data
        o_sl_rx_data                     : out std_logic_vector(255 downto 0);                    -- o_sl_rx_data
        i_sl_tx_error                    : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_error
        i_sl_tx_startofpacket            : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_startofpacket
        i_sl_tx_endofpacket              : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_endofpacket
        i_sl_tx_empty                    : in  std_logic_vector(11 downto 0)  := (others => 'X'); -- i_sl_tx_empty
        i_sl_tx_skip_crc                 : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_skip_crc
        o_sl_rx_startofpacket            : out std_logic_vector(3 downto 0);                      -- o_sl_rx_startofpacket
        o_sl_rx_endofpacket              : out std_logic_vector(3 downto 0);                      -- o_sl_rx_endofpacket
        o_sl_rx_empty                    : out std_logic_vector(11 downto 0);                     -- o_sl_rx_empty
        o_sl_rx_error                    : out std_logic_vector(23 downto 0);                     -- o_sl_rx_error
        o_sl_rxstatus_data               : out std_logic_vector(159 downto 0);                    -- o_sl_rxstatus_data
        o_sl_rxstatus_valid              : out std_logic_vector(3 downto 0);                      -- o_sl_rxstatus_valid
        i_sl_tx_pfc                      : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- i_sl_tx_pfc
        o_sl_rx_pfc                      : out std_logic_vector(31 downto 0);                     -- o_sl_rx_pfc
        i_sl_tx_pause                    : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_sl_tx_pause
        o_sl_rx_pause                    : out std_logic_vector(3 downto 0)                       -- o_sl_rx_pause
    );
    end component etile_eth_4x10g;

    -- =========================================================================
    --                               CONSTANTS
    -- =========================================================================
    constant LANES_PER_CHANNEL : natural := LANES/ETH_PORT_CHAN;

    constant MFB2AVST_FIFO_DEPTH    : natural := 512;

    -- AVST interface:
    constant AVST_DATA_WIDTH        : natural := tsel(ETH_PORT_SPEED = 100, 512, 64); -- 512 bits for "100g1" mode (one channel), 64 bits per channel for modes "25g4" and "10g4"
    constant AVST_EMPTY_WIDTH       : natural := tsel(ETH_PORT_SPEED = 100, 6  , 3 ); -- 6   bits for "100g1" mode (one channel), 3  bits per channel for modes "25g4" and "10g4"
    -- 6 bits per channel, it is not ETH_PORT_SPEED dependent
    constant RX_AVST_ERROR_WIDTH    : natural := 6;

    -- Number of MI Indirect Access' output interfaces
    --                                           eth inf       + xcvr inf + rsfec in case of 100g1 or 25g4
    constant IA_OUTPUT_INFS         : natural := ETH_PORT_CHAN + LANES    + tsel(ETH_PORT_SPEED = 10, 0, 1);

    constant MI_ADDR_BASES_PHY      : natural := ETH_PORT_CHAN + tsel(TS_DEMO_EN, 1, 0);
    constant MGMT_OFF               : std_logic_vector(MI_ADDR_WIDTH_PHY-1 downto 0) := X"0004_0000";

    function mi_addr_base_init_phy_f return slv_array_t is
        variable mi_addr_base_var : slv_array_t(MI_ADDR_BASES_PHY-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    begin
        for i in 0 to MI_ADDR_BASES_PHY-1 loop
            mi_addr_base_var(i) := std_logic_vector(resize(i*unsigned(MGMT_OFF), MI_ADDR_WIDTH_PHY));
        end loop;
        return mi_addr_base_var;
    end function;

    function speed_cap_f return std_logic_vector is
        variable speed_cap_v : std_logic_vector(15 downto 0);
    begin
        speed_cap_v := (others => '0');
        case ETH_PORT_SPEED is
            when 400 => speed_cap_v(15) := '1';
            when 200 => speed_cap_v(12) := '1';
            when 100 => speed_cap_v(9)  := '1';
            when 50  => speed_cap_v(3)  := '1';
            when 40  => speed_cap_v(8)  := '1';
            when 25  => speed_cap_v(11) := '1';
            when others => speed_cap_v(0)  := '1'; -- 10GE
        end case;
        return speed_cap_v;
    end function;

    -- Select the number of PCS lanes
    function pcs_lanes_num_f return natural is
    begin
        case ETH_PORT_SPEED is
            when 400 => return 16;
            when 200 => return 8;
            when 100 => return 20;
            when 50  => return 4;
            when 40  => return 4;
            when 25  => return 1;
            when 10  => return 1;
            when others  => return 1;
        end case;
    end function;

    -- Return FS-FEC ability for selected Ethernet type
    function rsfec_cap_f return std_logic is
        variable fec_cap : std_logic;
    begin
        fec_cap := '0';
        case ETH_PORT_SPEED is
            when 400 => fec_cap := '1';
            when 200 => fec_cap := '1';
            when 100 => fec_cap := '1';
            when 50  => fec_cap := '1';
            when 40  => fec_cap := '0';
            when 25  => fec_cap := '1';
            when others => fec_cap := '0'; -- 10GE
        end case;
        return fec_cap;
    end function;

    constant SPEED_CAP : std_logic_vector(16-1 downto 0) := speed_cap_f;
    constant RSFEC_CAP : std_logic                       := rsfec_cap_f;
    constant PCS_LANES : natural := pcs_lanes_num_f;

    -- =========================================================================
    --                                SIGNALS
    -- =========================================================================

    signal split_mi_dwr_phy  : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal split_mi_addr_phy : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    signal split_mi_rd_phy   : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);
    signal split_mi_wr_phy   : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);
    signal split_mi_be_phy   : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_DATA_WIDTH_PHY/8-1 downto 0);
    signal split_mi_ardy_phy : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);
    signal split_mi_drd_phy  : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal split_mi_drdy_phy : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);

    signal etile_clk_out_vec      : std_logic_vector(ETH_PORT_CHAN-1 downto 0); -- in case of multiple IP cores, only one is chosen
    signal etile_clk_out          : std_logic; -- drives i_clk_rx and i_clk_tx of one or more other IP cores

    signal tx_avst_data      : std_logic_vector(ETH_PORT_CHAN*AVST_DATA_WIDTH -1 downto 0);
    signal tx_avst_sop       : std_logic_vector(ETH_PORT_CHAN                 -1 downto 0);
    signal tx_avst_eop       : std_logic_vector(ETH_PORT_CHAN                 -1 downto 0);
    signal tx_avst_empty     : std_logic_vector(ETH_PORT_CHAN*AVST_EMPTY_WIDTH-1 downto 0);
    signal tx_avst_error     : std_logic_vector(ETH_PORT_CHAN                 -1 downto 0);
    signal tx_avst_valid     : std_logic_vector(ETH_PORT_CHAN                 -1 downto 0);
    signal tx_avst_ready     : std_logic_vector(ETH_PORT_CHAN                 -1 downto 0);

    signal tx_avst_data_arr  : slv_array_t(ETH_PORT_CHAN-1 downto 0)(AVST_DATA_WIDTH -1 downto 0);
    signal tx_avst_empty_arr : slv_array_t(ETH_PORT_CHAN-1 downto 0)(AVST_EMPTY_WIDTH-1 downto 0);

    signal rx_avst_data_arr  : slv_array_t(ETH_PORT_CHAN-1 downto 0)(AVST_DATA_WIDTH    -1 downto 0);
    signal rx_avst_empty_arr : slv_array_t(ETH_PORT_CHAN-1 downto 0)(AVST_EMPTY_WIDTH   -1 downto 0);
    signal rx_avst_error_arr : slv_array_t(ETH_PORT_CHAN-1 downto 0)(RX_AVST_ERROR_WIDTH-1 downto 0);

    signal rx_avst_data      : std_logic_vector(ETH_PORT_CHAN*AVST_DATA_WIDTH    -1 downto 0);
    signal rx_avst_valid     : std_logic_vector(ETH_PORT_CHAN                    -1 downto 0);
    signal rx_avst_sop       : std_logic_vector(ETH_PORT_CHAN                    -1 downto 0);
    signal rx_avst_eop       : std_logic_vector(ETH_PORT_CHAN                    -1 downto 0);
    signal rx_avst_empty     : std_logic_vector(ETH_PORT_CHAN*AVST_EMPTY_WIDTH   -1 downto 0);
    signal rx_avst_error     : std_logic_vector(ETH_PORT_CHAN*RX_AVST_ERROR_WIDTH-1 downto 0);

    -- Status signals
    signal rx_hi_ber         : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal rx_pcs_ready      : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal rx_block_lock     : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal rx_am_lock        : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal tx_lanes_stable   : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal ehip_ready        : std_logic_vector(LANES-1 downto 0);

    -- MI_PHY for E-tile reconfiguration interfaces (Ethernet, Transceiver (XCVR), RS-FEC)
    -- from MI Indirect Access (-> mi_ia_)
    signal mi_ia_dwr_phy  : slv_array_t     (IA_OUTPUT_INFS-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal mi_ia_addr_phy : slv_array_t     (IA_OUTPUT_INFS-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    signal mi_ia_rd_phy   : std_logic_vector(IA_OUTPUT_INFS-1 downto 0);
    signal mi_ia_wr_phy   : std_logic_vector(IA_OUTPUT_INFS-1 downto 0);
    signal mi_ia_ardy_phy : std_logic_vector(IA_OUTPUT_INFS-1 downto 0);
    signal mi_ia_drd_phy  : slv_array_t     (IA_OUTPUT_INFS-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal mi_ia_drdy_phy : std_logic_vector(IA_OUTPUT_INFS-1 downto 0);
    signal ia_ardy_vld    : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    -- eth reconfig interface
    signal eth_inf_dwr_phy          : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal eth_inf_dwr_phy_ser      : std_logic_vector(ETH_PORT_CHAN*            MI_DATA_WIDTH_PHY-1 downto 0);
    signal eth_inf_addr_phy         : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    signal eth_inf_addr_phy_res     : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(tsel(ETH_PORT_SPEED = 100, 21, 19)-1 downto 0);
    signal eth_inf_addr_phy_res_ser : std_logic_vector(ETH_PORT_CHAN*            tsel(ETH_PORT_SPEED = 100, 21, 19)-1 downto 0);
    signal eth_inf_rd_phy           : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal eth_inf_wr_phy           : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal eth_inf_ardy_phy_n       : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal eth_inf_drd_phy          : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal eth_inf_drd_phy_ser      : std_logic_vector(ETH_PORT_CHAN*            MI_DATA_WIDTH_PHY-1 downto 0);
    signal eth_inf_drdy_phy         : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    -- xcvr reconfig interface
    signal xcvr_inf_dwr_phy          : slv_array_t     (LANES-1 downto 0)(8                -1 downto 0);
    signal xcvr_inf_dwr_phy_res_ser  : std_logic_vector(LANES*            8                -1 downto 0);
    signal xcvr_inf_addr_phy         : slv_array_t     (LANES-1 downto 0)(19-1 downto 0);
    signal xcvr_inf_addr_phy_res_ser : std_logic_vector(LANES*            19-1 downto 0);
    signal xcvr_inf_rd_phy           : std_logic_vector(LANES-1 downto 0);
    signal xcvr_inf_wr_phy           : std_logic_vector(LANES-1 downto 0);
    signal xcvr_inf_ardy_phy_n       : std_logic_vector(LANES-1 downto 0);
    signal xcvr_inf_drd_phy          : slv_array_t     (LANES-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal xcvr_inf_drd_phy_res      : slv_array_t     (LANES-1 downto 0)(8                -1 downto 0);
    signal xcvr_inf_drd_phy_res_ser  : std_logic_vector(LANES*            8                -1 downto 0);
    signal init_lane_status          : slv_array_t(LANES-1 downto 0)(32-1 downto 0);
    -- rsfec reconfig interface
    signal rsfec_inf_dwr_phy      : std_logic_vector(MI_DATA_WIDTH_PHY-1 downto 0);
    signal rsfec_inf_dwr_phy_res  : std_logic_vector(8                -1 downto 0);
    signal rsfec_inf_addr_phy     : std_logic_vector(MI_ADDR_WIDTH_PHY-1 downto 0);
    signal rsfec_inf_addr_phy_res : std_logic_vector(11               -1 downto 0);
    signal rsfec_inf_rd_phy       : std_logic;
    signal rsfec_inf_wr_phy       : std_logic;
    signal rsfec_inf_ardy_phy_n   : std_logic;
    signal rsfec_inf_drd_phy      : std_logic_vector(MI_DATA_WIDTH_PHY-1 downto 0);
    signal rsfec_inf_drd_phy_res  : std_logic_vector(8                -1 downto 0);

    signal mgmt_pcs_reset : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal mgmt_pma_reset : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal mgmt_mac_loop  : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    -- Synchronization of REPEATER_CTRL
    signal sync_repeater_ctrl : std_logic_vector(ETH_PORT_CHAN-1 downto 0);

begin

    mi_splitter_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map(
        ADDR_WIDTH  => MI_ADDR_WIDTH_PHY,
        DATA_WIDTH  => MI_DATA_WIDTH_PHY,
        META_WIDTH  => 0,
        PORTS       => MI_ADDR_BASES_PHY,
        PIPE_OUT    => (others => true),
        PIPE_TYPE   => "REG",
        ADDR_BASES  => MI_ADDR_BASES_PHY,
        ADDR_BASE   => mi_addr_base_init_phy_f,
        DEVICE      => DEVICE
    )
    port map(
        CLK     => MI_CLK_PHY,
        RESET   => MI_RESET_PHY,

        RX_DWR  => MI_DWR_PHY,
        RX_MWR  => (others => '0'),
        RX_ADDR => MI_ADDR_PHY,
        RX_BE   => MI_BE_PHY,
        RX_RD   => MI_RD_PHY,
        RX_WR   => MI_WR_PHY,
        RX_ARDY => MI_ARDY_PHY,
        RX_DRD  => MI_DRD_PHY,
        RX_DRDY => MI_DRDY_PHY,

        TX_DWR  => split_mi_dwr_phy,
        TX_MWR  => open,
        TX_ADDR => split_mi_addr_phy,
        TX_BE   => split_mi_be_phy,
        TX_RD   => split_mi_rd_phy,
        TX_WR   => split_mi_wr_phy,
        TX_ARDY => split_mi_ardy_phy,
        TX_DRD  => split_mi_drd_phy,
        TX_DRDY => split_mi_drdy_phy
    );

    mgmt_g : for i in ETH_PORT_CHAN-1 downto 0 generate
        signal mgmt_pcs_control_i : std_logic_vector(16-1 downto 0);
        signal mgmt_pcs_status  : std_logic_vector(16-1 downto 0);
        signal mi_ia_drd    : std_logic_vector(MI_DATA_WIDTH_PHY-1 downto 0);
        signal mi_ia_drdy   : std_logic;
        signal mi_ia_en     : std_logic;
        signal mi_ia_we_phy : std_logic;
        signal mi_ia_sel    : std_logic_vector(4-1 downto 0);
        signal mi_ia_addr   : std_logic_vector(32-1 downto 0);
        signal mi_ia_dwr    : std_logic_vector(MI_DATA_WIDTH_PHY-1 downto 0);
        signal mi_ia_ardy   : std_logic;
        signal ia_rd_sel    : std_logic_vector(mi_ia_sel'range);
        signal ia_rd_sel_r  : std_logic_vector(mi_ia_sel'range);
        signal mgmt_pcs_control : std_logic_vector(16-1 downto 0);

        signal xcvr_init_status          : std_logic_vector(32-1 downto 0);
    begin

        mgmt_i : entity work.mgmt
        generic map (
            NUM_LANES     => PCS_LANES,
            PMA_LANES     => LANES_PER_CHANNEL,
            SPEED         => ETH_PORT_SPEED,
            SPEED_CAP     => SPEED_CAP,
            RSFEC_ABLE    => RSFEC_CAP,
            RSFEC_EN_INIT => RSFEC_CAP,
            AN_ABLE       => '0',
            DEVICE        => DEVICE,
            DRP_DWIDTH    => MI_DATA_WIDTH_PHY,
            DRP_AWIDTH    => 32
        )
        port map (
            RESET         => MI_RESET_PHY,
            MI_CLK        => MI_CLK_PHY,
            MI_DWR        => split_mi_dwr_phy(i),
            MI_ADDR       => split_mi_addr_phy(i),
            MI_RD         => split_mi_rd_phy(i),
            MI_WR         => split_mi_wr_phy(i),
            MI_BE         => split_mi_be_phy(i),
            MI_DRD        => split_mi_drd_phy(i),
            MI_ARDY       => split_mi_ardy_phy(i),
            MI_DRDY       => split_mi_drdy_phy(i),
            -- PCS status
            HI_BER        => rx_hi_ber(i),
            BLK_LOCK      => (others => rx_block_lock(i)),
            LINKSTATUS    => rx_pcs_ready(i) and not rx_hi_ber(i),
            BER_COUNT     => (others => '0'),
            BER_COUNT_CLR => open,
            BLK_ERR_CNTR  => (others => '0'),
            BLK_ERR_CLR   => open,
            SCR_BYPASS    => open,
            PCS_RESET     => mgmt_pcs_reset(i), --TODO
            PCS_LPBCK     => open,
            PCS_CONTROL   => mgmt_pcs_control,
            PCS_CONTROL_I => mgmt_pcs_control_i,
            PCS_STATUS    => mgmt_pcs_status,
            -- PCS Lane align
            ALGN_LOCKED   => rx_am_lock(i),
            BIP_ERR_CNTRS => (others => '0'),
            BIP_ERR_CLR   => open,
            LANE_MAP      => (others => '0'),
            LANE_ALIGN    => (others => rx_pcs_ready(i)),
            -- PMA & PMD status/control
            PMA_LOPWR     => open,
            PMA_LPBCK     => open,
            PMA_REM_LPBCK => open,
            PMA_RESET     => mgmt_pma_reset(i), --TODO
            PMA_RETUNE    => open,
            PMA_CONTROL   => open,
            PMA_STATUS    => xcvr_init_status,
            PMA_PTRN_EN   => open,
            PMA_TX_DIS    => open,
            PMA_RX_OK     => (others => rx_pcs_ready(i)), --TODO
            PMD_SIG_DET   => (others => rx_pcs_ready(i)), --TODO
            PMA_PRECURSOR => open,
            PMA_POSTCURSOR=> open,
            PMA_DRIVE     => open,
            -- Dynamic reconfiguration interface
            DRPCLK        => MI_CLK_PHY,
            DRPDO         => mi_ia_drd,
            DRPRDY        => mi_ia_drdy,
            DRPEN         => mi_ia_en,
            DRPWE         => mi_ia_we_phy,
            DRPADDR       => mi_ia_addr,
            DRPARDY       => mi_ia_ardy, --  and ia_ardy_vld, -- not working
            DRPDI         => mi_ia_dwr,
            DRPSEL        => mi_ia_sel
        );
        mgmt_mac_loop(i) <= mgmt_pcs_control(0);
        -- MDIO reg 3.4000 (vendor specific PCS control readout)
        mgmt_pcs_control_i(15 downto 1) <= (others => '0');
        mgmt_pcs_control_i(0)           <= sync_repeater_ctrl(i); -- MAC loopback active
        -- MDIO reg 3.4001 (vendor specific PCS status/abilities)
        mgmt_pcs_status(15 downto 1) <= (others => '0');
        mgmt_pcs_status(0)           <= '1';        -- MAC loopback ability supported

        -- Store mi_ia_sel for read operations
        sel_reg_p: process(MI_CLK_PHY)
        begin
            if rising_edge(MI_CLK_PHY) then
                ia_ardy_vld(i) <= mi_ia_en;
                if mi_ia_en = '1' then
                    ia_rd_sel_r <= mi_ia_sel;
                end if;
           end if;
        end process;
        ia_rd_sel <= mi_ia_sel when mi_ia_en = '1' else ia_rd_sel_r;

        -- Assign WR/RD signals for Eth blocks
        mi_ia_addr_phy(i)   <= mi_ia_addr(mi_ia_addr_phy(i)'range);
        mi_ia_dwr_phy(i)    <= mi_ia_dwr;
        mi_ia_wr_phy(i)     <= mi_ia_en and     mi_ia_we_phy when mi_ia_sel = "0000" else '0';
        mi_ia_rd_phy(i)     <= mi_ia_en and not mi_ia_we_phy when mi_ia_sel = "0000" else '0';
        -- Generate WR/RD signals for XCVR blocks
        xcvr_wr_rd_g: for xcvr in 0 to LANES_PER_CHANNEL-1 generate
            mi_ia_wr_phy  (xcvr + i*LANES_PER_CHANNEL + ETH_PORT_CHAN) <= mi_ia_en and     mi_ia_we_phy when mi_ia_sel = std_logic_vector(to_unsigned(xcvr+1,4)) else '0';
            mi_ia_rd_phy  (xcvr + i*LANES_PER_CHANNEL + ETH_PORT_CHAN) <= mi_ia_en and not mi_ia_we_phy when mi_ia_sel = std_logic_vector(to_unsigned(xcvr+1,4)) else '0';
            mi_ia_addr_phy(xcvr + i*LANES_PER_CHANNEL + ETH_PORT_CHAN) <= mi_ia_addr(mi_ia_addr_phy(i)'range);
            mi_ia_dwr_phy (xcvr + i*LANES_PER_CHANNEL + ETH_PORT_CHAN) <= mi_ia_dwr;
        end generate;
        rsfec_wr_rd_g: if (ETH_PORT_SPEED /= 10) and (i = 0) generate
            -- rsfec inf is on the last Output port of MI IA.
            -- Eth channel 0 is the only able to access the RS-FEC !
            mi_ia_wr_phy  (IA_OUTPUT_INFS-1) <= mi_ia_en and     mi_ia_we_phy when mi_ia_sel = "1001" else '0'; -- RS-FEC mapped to page 9
            mi_ia_rd_phy  (IA_OUTPUT_INFS-1) <= mi_ia_en and not mi_ia_we_phy when mi_ia_sel = "1001" else '0'; -- RS-FEC mapped to page 9
            mi_ia_addr_phy(IA_OUTPUT_INFS-1) <= mi_ia_addr(mi_ia_addr_phy(i)'range);
            mi_ia_dwr_phy (IA_OUTPUT_INFS-1) <= mi_ia_dwr;
        end generate;

        -- Mux read data from Eth/xvcr to mgmt
        drd_mux_p: process(all)
            variable mi_index     : integer range 0 to IA_OUTPUT_INFS-1;
            variable mi_index_vld : boolean;
            variable init_lane_index     : integer range 0 to LANES-1;
            variable init_lane_index_vld : boolean;
        begin
            mi_index_vld := False;

            case ia_rd_sel is
                when "0001" => -- XCVR0
                    mi_index_vld := True;
                    mi_index     := 0 + i*LANES_PER_CHANNEL + ETH_PORT_CHAN;
                when "0010" => -- XCVR1
                    if (LANES_PER_CHANNEL > 1) then
                        mi_index_vld := True;
                        mi_index     := 1 + i*LANES_PER_CHANNEL + ETH_PORT_CHAN;
                    end if;
                when "0011" => -- XCVR2
                    if (LANES_PER_CHANNEL > 2) then
                        mi_index_vld := True;
                        mi_index     := 2 + i*LANES_PER_CHANNEL + ETH_PORT_CHAN;
                    end if;
                when "0100" => -- XCVR3
                    if (LANES_PER_CHANNEL > 3) then
                        mi_index_vld := True;
                        mi_index     := 3 + i*LANES_PER_CHANNEL + ETH_PORT_CHAN;
                    end if;
                when "1001" => -- RS-FEC
                    mi_index_vld := True;
                    mi_index     := IA_OUTPUT_INFS-1;
                when others => -- "0000": Ethernet core
                    mi_index_vld := True;
                    mi_index     := i;
            end case;

            if (mi_index_vld) then
                mi_ia_drd  <= mi_ia_drd_phy (mi_index);
                mi_ia_drdy <= mi_ia_drdy_phy(mi_index);
                mi_ia_ardy <= mi_ia_ardy_phy(mi_index);
            else
                mi_ia_drd  <= (others => '0');
                mi_ia_drdy <= '0';
                mi_ia_ardy <= '0';
            end if;

            -- XCVR initialization debug - can be removed in the future to save some resources
            init_lane_index_vld := False;
            case mi_ia_sel is
                when "0010" =>
                    if (LANES_PER_CHANNEL > 1) then -- XCVR1
                        init_lane_index_vld := True;
                        init_lane_index     := 1 + i*LANES_PER_CHANNEL;
                    end if;
                when "0011" =>
                    if (LANES_PER_CHANNEL > 2) then -- XCVR2
                        init_lane_index_vld := True;
                        init_lane_index     := 2+ i*LANES_PER_CHANNEL;
                    end if;
                when "0100" =>
                    if (LANES_PER_CHANNEL > 3) then -- XCVR3
                        init_lane_index_vld := True;
                        init_lane_index     := 3 + i*LANES_PER_CHANNEL;
                    end if;
                when others =>
                    -- XCVR0
                    init_lane_index_vld := True;
                    init_lane_index     := 0 + i*LANES_PER_CHANNEL;
            end case;

            if (init_lane_index_vld) then
                xcvr_init_status <= init_lane_status(0 + i*LANES_PER_CHANNEL);
            else
                xcvr_init_status <= (others => '0');
            end if;
        end process;

    end generate;

    -- eth ---------------------------------------------------------------------
    eth_inf_dwr_phy  <= mi_ia_dwr_phy (ETH_PORT_CHAN-1 downto 0);
    eth_inf_addr_phy <= mi_ia_addr_phy(ETH_PORT_CHAN-1 downto 0);
    eth_inf_rd_phy   <= mi_ia_rd_phy  (ETH_PORT_CHAN-1 downto 0);
    eth_inf_wr_phy   <= mi_ia_wr_phy  (ETH_PORT_CHAN-1 downto 0);
    mi_ia_ardy_phy(ETH_PORT_CHAN-1 downto 0) <= not eth_inf_ardy_phy_n;
    mi_ia_drd_phy (ETH_PORT_CHAN-1 downto 0) <= eth_inf_drd_phy ;
    mi_ia_drdy_phy(ETH_PORT_CHAN-1 downto 0) <= eth_inf_drdy_phy;

    eth_inf_res_g: for i in ETH_PORT_CHAN-1 downto 0 generate
        eth_inf_addr_phy_res(i) <= eth_inf_addr_phy(i)(tsel(ETH_PORT_SPEED = 100, 21, 19)-1 downto 0);
    end generate;

    eth_inf_dwr_phy_ser      <= slv_array_ser(eth_inf_dwr_phy);
    eth_inf_addr_phy_res_ser <= slv_array_ser(eth_inf_addr_phy_res);
    eth_inf_drd_phy <= slv_array_deser(eth_inf_drd_phy_ser, ETH_PORT_CHAN);

    -- xcvr --------------------------------------------------------------------
    xcvr_reconfig_inf_res_g: for i in LANES-1 downto 0 generate
        signal init_busy      : std_logic;
        signal init_addr      : std_logic_vector(18 downto 0);
        signal init_read      : std_logic;
        signal init_write     : std_logic;
        signal init_writedata : std_logic_vector(31 downto 0);

        constant ETH_CHAN : natural := i / LANES_PER_CHANNEL;

    begin

        -- Arbitrage the xcvr_inf signals between XCVR_INIT and MGMT based on the init_busy signal:
        -- After power up or reset, the xcvr_inf bus is driven by the xcvr_init component to perform
        -- initialization of the e-tile transceivers. After the initialization finishes, the software is
        -- allowed to access this interface (via the MGMT)
        xcvr_inf_mux: process(all)
        begin
            if init_busy = '0' then
                mi_ia_drdy_phy(i + ETH_PORT_CHAN) <= xcvr_inf_rd_phy(i) and not xcvr_inf_ardy_phy_n(i);
                mi_ia_ardy_phy(i + ETH_PORT_CHAN) <= not xcvr_inf_ardy_phy_n(i);
                mi_ia_drd_phy (i + ETH_PORT_CHAN) <= xcvr_inf_drd_phy(i);
                xcvr_inf_rd_phy  (i) <= mi_ia_rd_phy(ETH_PORT_CHAN+i);
                xcvr_inf_wr_phy  (i) <= mi_ia_wr_phy(ETH_PORT_CHAN+i);
                xcvr_inf_dwr_phy (i) <= mi_ia_dwr_phy(ETH_PORT_CHAN+i)(8 -1 downto 0);
                xcvr_inf_addr_phy(i) <= mi_ia_addr_phy(ETH_PORT_CHAN+i)(19-1 downto 0);
            else
                mi_ia_drdy_phy(i + ETH_PORT_CHAN) <= '0';
                mi_ia_ardy_phy(i + ETH_PORT_CHAN) <= '0';
                mi_ia_drd_phy (i + ETH_PORT_CHAN) <= xcvr_inf_drd_phy(i);
                xcvr_inf_rd_phy  (i) <= init_read;
                xcvr_inf_wr_phy  (i) <= init_write;
                xcvr_inf_dwr_phy (i) <= init_writedata(8 -1 downto 0);
                xcvr_inf_addr_phy(i) <= init_addr;
            end if;
        end process;

        xcvr_inf_drd_phy(i)(MI_DATA_WIDTH_PHY-1 downto 8) <= (others => '0');
        xcvr_inf_drd_phy(i)(8-1 downto 0)                 <= xcvr_inf_drd_phy_res(i);

        xcvr_init: entity work.etile_xcvr_init
        port map (
            RST              => RESET_ETH or mgmt_pma_reset(ETH_CHAN),
            XCVR_RDY         => ehip_ready(i),
            CLK              => MI_CLK_PHY,
            BUSY             => init_busy,
            DONE             => open,
            -- AVMM
            ADDRESS          => init_addr,
            READ             => init_read,
            WRITE            => init_write,
            READDATA         => xcvr_inf_drd_phy(i),
            WRITEDATA        => init_writedata,
            WAITREQUEST      => xcvr_inf_ardy_phy_n(i),
            --
            STATE            => init_lane_status(i) -- TBD: debug purposes only. Can be left open in the future
         );

    end generate;

    xcvr_inf_dwr_phy_res_ser  <= slv_array_ser(xcvr_inf_dwr_phy);
    xcvr_inf_addr_phy_res_ser <= slv_array_ser(xcvr_inf_addr_phy);
    xcvr_inf_drd_phy_res <= slv_array_deser(xcvr_inf_drd_phy_res_ser, LANES);

    -- rsfec -------------------------------------------------------------------
    rsfec_inf_g: if (ETH_PORT_SPEED /= 10) generate
        -- rsfec inf is on the last Output port of MI IA
        rsfec_inf_dwr_phy  <= mi_ia_dwr_phy (IA_OUTPUT_INFS-1);
        rsfec_inf_addr_phy <= mi_ia_addr_phy(IA_OUTPUT_INFS-1);
        rsfec_inf_rd_phy   <= mi_ia_rd_phy  (IA_OUTPUT_INFS-1);
        rsfec_inf_wr_phy   <= mi_ia_wr_phy  (IA_OUTPUT_INFS-1);
        mi_ia_ardy_phy(IA_OUTPUT_INFS-1) <= not rsfec_inf_ardy_phy_n;
        mi_ia_drd_phy (IA_OUTPUT_INFS-1) <= rsfec_inf_drd_phy;
        mi_ia_drdy_phy(IA_OUTPUT_INFS-1) <= rsfec_inf_rd_phy and not rsfec_inf_ardy_phy_n; -- DRDY not used on the rsfec inf

        rsfec_inf_dwr_phy_res  <= rsfec_inf_dwr_phy (8 -1 downto 0);
        rsfec_inf_addr_phy_res <= rsfec_inf_addr_phy(11-1 downto 0);
        rsfec_inf_drd_phy(MI_DATA_WIDTH_PHY-1 downto 8) <= (others => '0');
        rsfec_inf_drd_phy(8-1 downto 0)                 <= rsfec_inf_drd_phy_res;
    end generate;

    -- =========================================================================
    -- The actual core
    -- =========================================================================
    eth_port_speed_sel_g : case ETH_PORT_SPEED generate

        when 100 =>
            -- =========================================================================
            -- E-TILE Ethernet
            -- =========================================================================
            etile_eth_ip_i : component etile_eth_1x100g
            generic map (
                am_encoding40g_0              => 9467463,
                am_encoding40g_1              => 15779046,
                am_encoding40g_2              => 12936603,
                am_encoding40g_3              => 10647869,
                enforce_max_frame_size        => "disable",
                flow_control                  => "both_no_xoff",
                flow_control_holdoff_mode     => "uniform",
                forward_rx_pause_requests     => "disable",
                hi_ber_monitor                => "enable",
                holdoff_quanta                => 65535,
                ipg_removed_per_am_period     => 20,
                link_fault_mode               => "lf_bidir", --"lf_off",
                pause_quanta                  => 65535,
                pfc_holdoff_quanta_0          => 65535,
                pfc_holdoff_quanta_1          => 65535,
                pfc_holdoff_quanta_2          => 65535,
                pfc_holdoff_quanta_3          => 65535,
                pfc_holdoff_quanta_4          => 65535,
                pfc_holdoff_quanta_5          => 65535,
                pfc_holdoff_quanta_6          => 65535,
                pfc_holdoff_quanta_7          => 65535,
                pfc_pause_quanta_0            => 65535,
                pfc_pause_quanta_1            => 65535,
                pfc_pause_quanta_2            => 65535,
                pfc_pause_quanta_3            => 65535,
                pfc_pause_quanta_4            => 65535,
                pfc_pause_quanta_5            => 65535,
                pfc_pause_quanta_6            => 65535,
                pfc_pause_quanta_7            => 65535,
                remove_pads                   => "disable",
                rx_length_checking            => "disable",
                rx_max_frame_size             => 16383,
                rx_pause_daddr                => "17483607389996",
                rx_pcs_max_skew               => 47,
                rx_vlan_detection             => "disable",
                rxcrc_covers_preamble         => "disable",
                sim_mode                      => "enable",
                source_address_insertion      => "disable",
                strict_preamble_checking      => "disable",
                strict_sfd_checking           => "disable",
                tx_ipg_size                   => "ipg_12",
                tx_max_frame_size             => 16383,
                tx_pause_daddr                => "1652522221569",
                tx_pause_saddr                => "247393538562781",
                tx_pld_fifo_almost_full_level => 16,
                tx_vlan_detection             => "disable",
                txcrc_covers_preamble         => "disable",
                txmac_saddr                   => "73588229205",
                uniform_holdoff_quanta        => 51090,
                flow_control_sl_0             => "both_no_xoff"
            )
            port map (
                i_stats_snapshot              => '1',
                o_cdr_lock                    => open,
                o_tx_pll_locked               => open,
                -- Eth reconfig inf (0x0)
                i_eth_reconfig_addr           => eth_inf_addr_phy_res_ser,
                i_eth_reconfig_read           => eth_inf_rd_phy(0),
                i_eth_reconfig_write          => eth_inf_wr_phy(0),
                o_eth_reconfig_readdata       => eth_inf_drd_phy_ser,
                o_eth_reconfig_readdata_valid => eth_inf_drdy_phy(0),
                i_eth_reconfig_writedata      => eth_inf_dwr_phy_ser,
                o_eth_reconfig_waitrequest    => eth_inf_ardy_phy_n(0),
                -- RS-FEC reconfig inf (0x5)
                i_rsfec_reconfig_addr         => rsfec_inf_addr_phy_res,
                i_rsfec_reconfig_read         => rsfec_inf_rd_phy,
                i_rsfec_reconfig_write        => rsfec_inf_wr_phy,
                o_rsfec_reconfig_readdata     => rsfec_inf_drd_phy_res,
                i_rsfec_reconfig_writedata    => rsfec_inf_dwr_phy_res,
                o_rsfec_reconfig_waitrequest  => rsfec_inf_ardy_phy_n,
                o_tx_lanes_stable             => tx_lanes_stable(0),
                o_rx_pcs_ready                => rx_pcs_ready(0),
                o_ehip_ready                  => ehip_ready(0),
                o_rx_block_lock               => rx_block_lock(0),
                o_rx_am_lock                  => rx_am_lock(0),
                o_rx_hi_ber                   => rx_hi_ber(0),
                o_local_fault_status          => open,
                o_remote_fault_status         => open,
                i_clk_ref                     => (others => QSFP_REFCLK_P),
                i_clk_tx                      => etile_clk_out,
                i_clk_rx                      => etile_clk_out,
                o_clk_pll_div64               => etile_clk_out_vec, -- o_clk_pll_div64 is reliable only after o_tx_pll_locked is asserted
                o_clk_pll_div66               => open,
                o_clk_rec_div64               => open,
                o_clk_rec_div66               => open,
                i_csr_rst_n                   => not RESET_ETH,
                i_tx_rst_n                    => '1',
                i_rx_rst_n                    => '1',
                o_tx_serial                   => QSFP_TX_P,
                i_rx_serial                   => QSFP_RX_P,
                o_tx_serial_n                 => QSFP_TX_N,
                i_rx_serial_n                 => QSFP_RX_N,
                i_reconfig_clk                => MI_CLK_PHY,
                i_reconfig_reset              => MI_RESET_PHY,
                -- XCVR reconfig inf (0x4 downto 0x1)
                i_xcvr_reconfig_address       => xcvr_inf_addr_phy_res_ser,
                i_xcvr_reconfig_read          => xcvr_inf_rd_phy,
                i_xcvr_reconfig_write         => xcvr_inf_wr_phy,
                o_xcvr_reconfig_readdata      => xcvr_inf_drd_phy_res_ser,
                i_xcvr_reconfig_writedata     => xcvr_inf_dwr_phy_res_ser,
                o_xcvr_reconfig_waitrequest   => xcvr_inf_ardy_phy_n,
                o_tx_ready                    => tx_avst_ready(0),
                i_tx_valid                    => tx_avst_valid(0),
                i_tx_data                     => tx_avst_data,
                i_tx_error                    => tx_avst_error(0),
                i_tx_startofpacket            => tx_avst_sop(0),
                i_tx_endofpacket              => tx_avst_eop(0),
                i_tx_empty                    => tx_avst_empty,
                i_tx_skip_crc                 => '0',
                o_rx_valid                    => rx_avst_valid(0),
                o_rx_data                     => rx_avst_data,
                o_rx_startofpacket            => rx_avst_sop(0),
                o_rx_endofpacket              => rx_avst_eop(0),
                o_rx_empty                    => rx_avst_empty,
                o_rx_error                    => rx_avst_error,
                o_rxstatus_data               => open,
                o_rxstatus_valid              => open,
                i_tx_pfc                      => (others => '0'),
                o_rx_pfc                      => open,
                i_tx_pause                    => '0',
                o_rx_pause                    => open
            );

            ehip_ready(LANES-1 downto 1) <= (others => ehip_ready(0));

        when 25 =>

            -- =========================================================================
            -- E-TILE Ethernet
            -- =========================================================================
            etile_eth_ip_i : component etile_eth_4x25g
            generic map (
                am_encoding40g_0              => 9467463,
                am_encoding40g_1              => 15779046,
                am_encoding40g_2              => 12936603,
                am_encoding40g_3              => 10647869,
                enforce_max_frame_size        => "disable",
                flow_control                  => "both_no_xoff",
                flow_control_holdoff_mode     => "uniform",
                forward_rx_pause_requests     => "disable",
                hi_ber_monitor                => "enable",
                holdoff_quanta                => 65535,
                ipg_removed_per_am_period     => 20,
                link_fault_mode               => "lf_bidir",
                pause_quanta                  => 65535,
                pfc_holdoff_quanta_0          => 32768,
                pfc_holdoff_quanta_1          => 32768,
                pfc_holdoff_quanta_2          => 32768,
                pfc_holdoff_quanta_3          => 32768,
                pfc_holdoff_quanta_4          => 32768,
                pfc_holdoff_quanta_5          => 32768,
                pfc_holdoff_quanta_6          => 32768,
                pfc_holdoff_quanta_7          => 32768,
                pfc_pause_quanta_0            => 65535,
                pfc_pause_quanta_1            => 65535,
                pfc_pause_quanta_2            => 65535,
                pfc_pause_quanta_3            => 65535,
                pfc_pause_quanta_4            => 65535,
                pfc_pause_quanta_5            => 65535,
                pfc_pause_quanta_6            => 65535,
                pfc_pause_quanta_7            => 65535,
                remove_pads                   => "disable",
                rx_length_checking            => "disable",
                rx_max_frame_size             => 16383,
                rx_pause_daddr                => "17483607389996",
                rx_pcs_max_skew               => 47,
                rx_vlan_detection             => "disable",
                rxcrc_covers_preamble         => "disable",
                sim_mode                      => "enable",
                source_address_insertion      => "disable",
                strict_preamble_checking      => "disable",
                strict_sfd_checking           => "disable",
                tx_ipg_size                   => "ipg_12",
                tx_max_frame_size             => 16383,
                tx_pause_daddr                => "1652522221569",
                tx_pause_saddr                => "73588229205",
                tx_pld_fifo_almost_full_level => 16,
                tx_vlan_detection             => "disable",
                txcrc_covers_preamble         => "disable",
                txmac_saddr                   => "73588229205",
                uniform_holdoff_quanta        => 51090,
                flow_control_sl_0             => "both_no_xoff"
            )
            port map (
                o_cdr_lock                       => open,
                o_tx_pll_locked                  => open,
                -- RS-FEC reconfig inf (0x8)
                i_rsfec_reconfig_addr            => rsfec_inf_addr_phy_res,
                i_rsfec_reconfig_read            => rsfec_inf_rd_phy,
                i_rsfec_reconfig_write           => rsfec_inf_wr_phy,
                o_rsfec_reconfig_readdata        => rsfec_inf_drd_phy_res,
                i_rsfec_reconfig_writedata       => rsfec_inf_dwr_phy_res,
                o_rsfec_reconfig_waitrequest     => rsfec_inf_ardy_phy_n,
                i_clk_ref                        => (others => QSFP_REFCLK_P),
                o_clk_pll_div64                  => etile_clk_out_vec,
                o_clk_pll_div66                  => open,
                o_clk_rec_div64                  => open,
                o_clk_rec_div66                  => open,
                o_tx_serial                      => QSFP_TX_P,
                i_rx_serial                      => QSFP_RX_P,
                o_tx_serial_n                    => QSFP_TX_N,
                i_rx_serial_n                    => QSFP_RX_N,
                i_reconfig_clk                   => MI_CLK_PHY,
                i_reconfig_reset                 => MI_RESET_PHY,
                -- XCVR reconfig inf (0x7 downto 0x4)
                i_xcvr_reconfig_address          => xcvr_inf_addr_phy_res_ser,
                i_xcvr_reconfig_read             => xcvr_inf_rd_phy,
                i_xcvr_reconfig_write            => xcvr_inf_wr_phy,
                o_xcvr_reconfig_readdata         => xcvr_inf_drd_phy_res_ser,
                i_xcvr_reconfig_writedata        => xcvr_inf_dwr_phy_res_ser,
                o_xcvr_reconfig_waitrequest      => xcvr_inf_ardy_phy_n,
                i_sl_stats_snapshot              => (others => '1'),
                o_sl_rx_hi_ber                   => rx_hi_ber, -- enabled in generics
                -- Eth reconfig inf (0x3 downto 0x0)
                i_sl_eth_reconfig_addr           => eth_inf_addr_phy_res_ser,
                i_sl_eth_reconfig_read           => eth_inf_rd_phy,
                i_sl_eth_reconfig_write          => eth_inf_wr_phy,
                o_sl_eth_reconfig_readdata       => eth_inf_drd_phy_ser,
                o_sl_eth_reconfig_readdata_valid => eth_inf_drdy_phy,
                i_sl_eth_reconfig_writedata      => eth_inf_dwr_phy_ser,
                o_sl_eth_reconfig_waitrequest    => eth_inf_ardy_phy_n,
                o_sl_tx_lanes_stable             => tx_lanes_stable,
                o_sl_rx_pcs_ready                => rx_pcs_ready,
                o_sl_ehip_ready                  => ehip_ready,
                o_sl_rx_block_lock               => rx_block_lock,
                o_sl_local_fault_status          => open,
                o_sl_remote_fault_status         => open,
                i_sl_clk_tx                      => (others => etile_clk_out),
                i_sl_clk_rx                      => (others => etile_clk_out),
                i_sl_csr_rst_n                   => (others => not RESET_ETH),
                i_sl_tx_rst_n                    => (others => '1'),
                i_sl_rx_rst_n                    => (others => '1'),
                o_sl_txfifo_pfull                => open,
                o_sl_txfifo_pempty               => open,
                o_sl_txfifo_overflow             => open,
                o_sl_txfifo_underflow            => open,
                o_sl_tx_ready                    => tx_avst_ready,
                o_sl_rx_valid                    => rx_avst_valid,
                i_sl_tx_valid                    => tx_avst_valid,
                i_sl_tx_data                     => tx_avst_data,
                o_sl_rx_data                     => rx_avst_data,
                i_sl_tx_error                    => tx_avst_error,
                i_sl_tx_startofpacket            => tx_avst_sop,
                i_sl_tx_endofpacket              => tx_avst_eop,
                i_sl_tx_empty                    => tx_avst_empty,
                i_sl_tx_skip_crc                 => (others => '0'),
                o_sl_rx_startofpacket            => rx_avst_sop,
                o_sl_rx_endofpacket              => rx_avst_eop,
                o_sl_rx_empty                    => rx_avst_empty,
                o_sl_rx_error                    => rx_avst_error,
                o_sl_rxstatus_data               => open,
                o_sl_rxstatus_valid              => open,
                i_sl_tx_pfc                      => (others => '0'),
                o_sl_rx_pfc                      => open,
                i_sl_tx_pause                    => (others => '0'),
                o_sl_rx_pause                    => open
            );


        when 10 =>

            -- =========================================================================
            -- E-TILE Ethernet
            -- =========================================================================
            etile_eth_ip_i : component etile_eth_4x10g
            generic map (
                am_encoding40g_0              => 9467463,
                am_encoding40g_1              => 15779046,
                am_encoding40g_2              => 12936603,
                am_encoding40g_3              => 10647869,
                enforce_max_frame_size        => "disable",
                flow_control                  => "both_no_xoff",
                flow_control_holdoff_mode     => "per_queue",
                forward_rx_pause_requests     => "disable",
                hi_ber_monitor                => "enable",
                holdoff_quanta                => 65535,
                ipg_removed_per_am_period     => 20,
                link_fault_mode               => "lf_bidir",
                pause_quanta                  => 65535,
                pfc_holdoff_quanta_0          => 32768,
                pfc_holdoff_quanta_1          => 32768,
                pfc_holdoff_quanta_2          => 32768,
                pfc_holdoff_quanta_3          => 32768,
                pfc_holdoff_quanta_4          => 32768,
                pfc_holdoff_quanta_5          => 32768,
                pfc_holdoff_quanta_6          => 32768,
                pfc_holdoff_quanta_7          => 32768,
                pfc_pause_quanta_0            => 65535,
                pfc_pause_quanta_1            => 65535,
                pfc_pause_quanta_2            => 65535,
                pfc_pause_quanta_3            => 65535,
                pfc_pause_quanta_4            => 65535,
                pfc_pause_quanta_5            => 65535,
                pfc_pause_quanta_6            => 65535,
                pfc_pause_quanta_7            => 65535,
                remove_pads                   => "disable",
                rx_length_checking            => "enable",
                rx_max_frame_size             => 16383,
                rx_pause_daddr                => "1652522221569",
                rx_pcs_max_skew               => 47,
                rx_vlan_detection             => "disable",
                rxcrc_covers_preamble         => "disable",
                sim_mode                      => "enable",
                source_address_insertion      => "disable",
                strict_preamble_checking      => "disable",
                strict_sfd_checking           => "disable",
                tx_ipg_size                   => "ipg_12",
                tx_max_frame_size             => 16383,
                tx_pause_daddr                => "1652522221569",
                tx_pause_saddr                => "73588229205",
                tx_pld_fifo_almost_full_level => 16,
                tx_vlan_detection             => "disable",
                txcrc_covers_preamble         => "disable",
                txmac_saddr                   => "73588229205",
                uniform_holdoff_quanta        => 65535,
                flow_control_sl_0             => "both_no_xoff"
            )
            port map (
                o_cdr_lock                       => open,
                o_tx_pll_locked                  => open,
                i_clk_ref                        => (others => QSFP_REFCLK_P),
                o_clk_pll_div64                  => etile_clk_out_vec,
                o_clk_pll_div66                  => open,
                o_clk_rec_div64                  => open,
                o_clk_rec_div66                  => open,
                o_tx_serial                      => QSFP_TX_P,
                i_rx_serial                      => QSFP_RX_P,
                o_tx_serial_n                    => QSFP_TX_N,
                i_rx_serial_n                    => QSFP_RX_N,
                i_reconfig_clk                   => MI_CLK_PHY,
                i_reconfig_reset                 => MI_RESET_PHY,
                -- XCVR reconfig inf (0x7 downto 0x4)
                i_xcvr_reconfig_address          => xcvr_inf_addr_phy_res_ser,
                i_xcvr_reconfig_read             => xcvr_inf_rd_phy,
                i_xcvr_reconfig_write            => xcvr_inf_wr_phy,
                o_xcvr_reconfig_readdata         => xcvr_inf_drd_phy_res_ser,
                i_xcvr_reconfig_writedata        => xcvr_inf_dwr_phy_res_ser,
                o_xcvr_reconfig_waitrequest      => xcvr_inf_ardy_phy_n,
                i_sl_stats_snapshot              => (others => '1'),
                o_sl_rx_hi_ber                   => rx_hi_ber, -- enabled in generics
                -- Eth reconfig inf (0x3 downto 0x0)
                i_sl_eth_reconfig_addr           => eth_inf_addr_phy_res_ser,
                i_sl_eth_reconfig_read           => eth_inf_rd_phy,
                i_sl_eth_reconfig_write          => eth_inf_wr_phy,
                o_sl_eth_reconfig_readdata       => eth_inf_drd_phy_ser,
                o_sl_eth_reconfig_readdata_valid => eth_inf_drdy_phy,
                i_sl_eth_reconfig_writedata      => eth_inf_dwr_phy_ser,
                o_sl_eth_reconfig_waitrequest    => eth_inf_ardy_phy_n,
                o_sl_tx_lanes_stable             => tx_lanes_stable,
                o_sl_rx_pcs_ready                => rx_pcs_ready,
                o_sl_ehip_ready                  => ehip_ready,
                o_sl_rx_block_lock               => rx_block_lock,
                o_sl_local_fault_status          => open,
                o_sl_remote_fault_status         => open,
                i_sl_clk_tx                      => (others => etile_clk_out),
                i_sl_clk_rx                      => (others => etile_clk_out),
                i_sl_csr_rst_n                   => (others => not RESET_ETH),
                i_sl_tx_rst_n                    => (others => '1'),
                i_sl_rx_rst_n                    => (others => '1'),
                o_sl_txfifo_pfull                => open,
                o_sl_txfifo_pempty               => open,
                o_sl_txfifo_overflow             => open,
                o_sl_txfifo_underflow            => open,
                o_sl_tx_ready                    => tx_avst_ready,
                o_sl_rx_valid                    => rx_avst_valid,
                i_sl_tx_valid                    => tx_avst_valid,
                i_sl_tx_data                     => tx_avst_data,
                o_sl_rx_data                     => rx_avst_data,
                i_sl_tx_error                    => tx_avst_error,
                i_sl_tx_startofpacket            => tx_avst_sop,
                i_sl_tx_endofpacket              => tx_avst_eop,
                i_sl_tx_empty                    => tx_avst_empty,
                i_sl_tx_skip_crc                 => (others => '0'),
                o_sl_rx_startofpacket            => rx_avst_sop,
                o_sl_rx_endofpacket              => rx_avst_eop,
                o_sl_rx_empty                    => rx_avst_empty,
                o_sl_rx_error                    => rx_avst_error,
                o_sl_rxstatus_data               => open,
                o_sl_rxstatus_valid              => open,
                i_sl_tx_pfc                      => (others => '0'),
                o_sl_rx_pfc                      => open,
                i_sl_tx_pause                    => (others => '0'),
                o_sl_rx_pause                    => open
            );

        when others =>
            assert (True) report "Unsupported case" severity failure;

    end generate;

     -- =========================================================================
     -- ADAPTERS
     -- =========================================================================
     etile_clk_out <= etile_clk_out_vec(0);
     CLK_ETH       <= etile_clk_out;

     -- TX adaption -------------------------------------------------------------
     tx_avst_data  <= slv_array_ser(tx_avst_data_arr);
     tx_avst_empty <= slv_array_ser(tx_avst_empty_arr);

    -- RX adaption -------------------------------------------------------------
    rx_avst_data_arr  <= slv_array_deser(rx_avst_data , ETH_PORT_CHAN);
    rx_avst_empty_arr <= slv_array_deser(rx_avst_empty, ETH_PORT_CHAN);
    rx_avst_error_arr <= slv_array_deser(rx_avst_error, ETH_PORT_CHAN);

    adapter_g : for IT in ETH_PORT_CHAN-1 downto 0 generate
        signal mfb2avst_rx_mfb_sof : std_logic_vector(1-1 downto 0);
        signal mfb2avst_rx_mfb_eof : std_logic_vector(1-1 downto 0);

        signal tx_ad_avst_data   : std_logic_vector(AVST_DATA_WIDTH -1 downto 0);
        signal tx_ad_avst_sop    : std_logic;
        signal tx_ad_avst_eop    : std_logic;
        signal tx_ad_avst_empty  : std_logic_vector(AVST_EMPTY_WIDTH-1 downto 0);
        signal tx_ad_avst_error  : std_logic;
        signal tx_ad_avst_valid  : std_logic;

        signal tx_loop_avst_data   : std_logic_vector(AVST_DATA_WIDTH -1 downto 0);
        signal tx_loop_avst_sop    : std_logic;
        signal tx_loop_avst_eop    : std_logic;
        signal tx_loop_avst_empty  : std_logic_vector(AVST_EMPTY_WIDTH-1 downto 0);
        signal tx_loop_avst_error  : std_logic;
        signal tx_loop_avst_valid  : std_logic;
    begin

        process(RX_MFB_SOF, RX_MFB_EOF)
        begin
            mfb2avst_rx_mfb_sof <= RX_MFB_SOF(IT);
            mfb2avst_rx_mfb_eof <= RX_MFB_EOF(IT);
        end process;

        -- TX adaption
        mfb2avst_i : entity work.TX_MAC_LITE_ADAPTER_AVST_100G
        generic map(
            DATA_WIDTH => AVST_DATA_WIDTH,
            FIFO_DEPTH => MFB2AVST_FIFO_DEPTH,
            DEVICE     => DEVICE
        )
        port map(
            CLK            => etile_clk_out,
            RESET          => RESET_ETH    ,

            RX_MFB_DATA    => RX_MFB_DATA   (IT),
            RX_MFB_SOF     => mfb2avst_rx_mfb_sof,
            RX_MFB_SOF_POS => RX_MFB_SOF_POS(IT),
            RX_MFB_EOF     => mfb2avst_rx_mfb_eof,
            RX_MFB_EOF_POS => RX_MFB_EOF_POS(IT),
            RX_MFB_SRC_RDY => RX_MFB_SRC_RDY(IT),
            RX_MFB_DST_RDY => RX_MFB_DST_RDY(IT),

            TX_AVST_DATA   => tx_ad_avst_data,
            TX_AVST_SOP    => tx_ad_avst_sop,
            TX_AVST_EOP    => tx_ad_avst_eop,
            TX_AVST_EMPTY  => tx_ad_avst_empty,
            TX_AVST_ERROR  => tx_ad_avst_error,
            TX_AVST_VALID  => tx_ad_avst_valid,
            TX_AVST_READY  => tx_avst_ready(IT)
        );

        -- RX adaption
        avst2mfb_i : entity work.ETH_AVST_ADAPTER
        generic map(
            DATA_WIDTH     => AVST_DATA_WIDTH,
            TX_REGION_SIZE => AVST_DATA_WIDTH/64
        )
        port map(
            CLK              => etile_clk_out,
            RESET            => RESET_ETH    ,

            IN_AVST_DATA     => rx_avst_data_arr (IT),
            IN_AVST_SOP      => rx_avst_sop      (IT),
            IN_AVST_EOP      => rx_avst_eop      (IT),
            IN_AVST_EMPTY    => rx_avst_empty_arr(IT),
            IN_AVST_ERROR    => rx_avst_error_arr(IT),
            IN_AVST_VALID    => rx_avst_valid    (IT),
            IN_RX_PCS_READY  => '0', -- rx_pcs_ready (0)
            IN_RX_BLOCK_LOCK => '0', -- rx_block_lock(0)
            IN_RX_AM_LOCK    => '0', -- rx_am_lock   (0)

            OUT_MFB_DATA     => TX_MFB_DATA   (IT),
            OUT_MFB_SOF      => TX_MFB_SOF    (IT),
            OUT_MFB_SOF_POS  => TX_MFB_SOF_POS(IT),
            OUT_MFB_EOF      => TX_MFB_EOF    (IT),
            OUT_MFB_EOF_POS  => TX_MFB_EOF_POS(IT),
            OUT_MFB_ERROR    => TX_MFB_ERROR  (IT),
            OUT_MFB_SRC_RDY  => TX_MFB_SRC_RDY(IT),
            OUT_LINK_UP      => open -- this is done here
        );


        repeater_i: entity work.avst_loop
        generic map (
            SEGMENTS => AVST_DATA_WIDTH/64
        )
        port map (
            RST              => RESET_ETH,
            CLK              => etile_clk_out,
            --
            IN_AVST_DATA     => rx_avst_data_arr(IT),
            IN_AVST_SOP      => rx_avst_sop(IT),
            IN_AVST_EOP      => rx_avst_eop(IT),
            IN_AVST_EMPTY    => rx_avst_empty_arr(IT),
            IN_AVST_VALID    => rx_avst_valid(IT),
            -- OUTPUT AVST INTERFACE (Intel E-Tile Ethernet IP)
            TX_AVST_DATA     => tx_loop_avst_data,
            TX_AVST_SOP      => tx_loop_avst_sop,
            TX_AVST_EOP      => tx_loop_avst_eop,
            TX_AVST_EMPTY    => tx_loop_avst_empty,
            TX_AVST_VALID    => tx_loop_avst_valid,
            TX_AVST_READY    => tx_avst_ready(IT)
        );
        tx_loop_avst_error <= '0';

        eth_tx_mux: process(all)
        begin
            if sync_repeater_ctrl(IT) = '1' then
                -- MAC loopback on
                tx_avst_data_arr(IT)  <= tx_loop_avst_data;
                tx_avst_sop(IT)       <= tx_loop_avst_sop;
                tx_avst_eop(IT)       <= tx_loop_avst_eop;
                tx_avst_empty_arr(IT) <= tx_loop_avst_empty;
                tx_avst_error(IT)     <= tx_loop_avst_error;
                tx_avst_valid(IT)     <= tx_loop_avst_valid;
            else
                -- MAC loopback off
                tx_avst_data_arr(IT)  <= tx_ad_avst_data;
                tx_avst_sop(IT)       <= tx_ad_avst_sop;
                tx_avst_eop(IT)       <= tx_ad_avst_eop;
                tx_avst_empty_arr(IT) <= tx_ad_avst_empty;
                tx_avst_error(IT)     <= tx_ad_avst_error;
                tx_avst_valid(IT)     <= tx_ad_avst_valid;
            end if;
        end process;
    end generate;

    process(etile_clk_out)
    begin
        if rising_edge(etile_clk_out) then
            if (RESET_ETH = '1') then
                RX_LINK_UP <= (others => '0');
                TX_LINK_UP <= (others => '0');
            else
                RX_LINK_UP <= rx_pcs_ready and rx_block_lock and rx_am_lock;
                TX_LINK_UP <= tx_lanes_stable;
            end if;
        end if;
    end process;


    -- Synchronization of REPEATER_CTRL
    sync_repeater_ctrl_i : entity work.ASYNC_BUS_HANDSHAKE
    generic map (
        DATA_WIDTH => ETH_PORT_CHAN
    ) port map (
        ACLK       => MI_CLK_PHY,
        ARST       => MI_RESET_PHY,
        ADATAIN    => mgmt_mac_loop,
        ASEND      => '1',
        AREADY     => open,
        BCLK       => etile_clk_out,
        BRST       => '0',
        BDATAOUT   => sync_repeater_ctrl,
        BLOAD      => '1',
        BVALID     => open
    );

    -- =====================================================================
    -- Timestamp-limiting demo/testing logic
    -- =====================================================================

    ts_demo_en_g : if TS_DEMO_EN generate

        ts_demo_logic_i: entity work.TS_DEMO_LOGIC
        generic map (
            REGIONS         => REGIONS          ,
            ETH_PORT_CHAN   => ETH_PORT_CHAN    ,
            MI_DATA_WIDTH   => MI_DATA_WIDTH_PHY,
            MI_ADDR_WIDTH   => MI_ADDR_WIDTH_PHY,
            TX_DMA_CHANNELS => TX_DMA_CHANNELS  ,
            DEVICE          => DEVICE
        )
        port map (
            CLK_ETH       => CLK_ETH                               ,
            RESET_ETH     => RESET_ETH                             ,

            CORE_SOP      => tx_avst_sop                           ,
            CORE_SRC_RDY  => tx_avst_valid                         ,
            CORE_DST_RDY  => tx_avst_ready                         ,

            APP_CHANNEL   => RX_MVB_CHANNEL                        ,
            APP_TIMESTAMP => RX_MVB_TIMESTAMP                      ,
            APP_VLD       => RX_MVB_VLD                            ,

            TSU_TS_NS     => TSU_TS_NS                             ,
            TSU_TS_DV     => TSU_TS_DV                             ,

            MI_CLK        => MI_CLK_PHY                            ,
            MI_RESET      => MI_RESET_PHY                          ,

            MI_DWR        => split_mi_dwr_phy (MI_ADDR_BASES_PHY-1),
            MI_ADDR       => split_mi_addr_phy(MI_ADDR_BASES_PHY-1),
            MI_RD         => split_mi_rd_phy  (MI_ADDR_BASES_PHY-1),
            MI_WR         => split_mi_wr_phy  (MI_ADDR_BASES_PHY-1),
            MI_BE         => split_mi_be_phy  (MI_ADDR_BASES_PHY-1),
            MI_DRD        => split_mi_drd_phy (MI_ADDR_BASES_PHY-1),
            MI_ARDY       => split_mi_ardy_phy(MI_ADDR_BASES_PHY-1),
            MI_DRDY       => split_mi_drdy_phy(MI_ADDR_BASES_PHY-1)
        );

    end generate;

end architecture;
