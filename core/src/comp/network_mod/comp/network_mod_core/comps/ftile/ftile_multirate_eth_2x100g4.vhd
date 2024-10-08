-- ftile_multirate_eth_2x100g4: Component declaration for F-Tile Multirate IP 2 x 100g4 (lines) core
-- Base profile 100g-4 NOFEC Secondary profile 100g-4 FEC
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Jakub Záhora <xzahor06@vutbr.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity FTILE_MULTIRATE_ETH_2x100G4 is
    generic(
        -- ===================================================================
        -- Multirate generic param from NMC (eneable for generating DRP)
        -- ===================================================================
        IP_CNT              : natural := 0
    );
    port (
        -- ===================================================================
        -- MGMT Interface
        -- ===================================================================
        -- MI32 Interface
        MI_RESET_PHY             : in  std_logic;
        MI_CLK_PHY               : in  std_logic;
        MI_DWR                   : in  std_logic_vector(31 downto 0);
        MI_ADDR                  : in  std_logic_vector(31 downto 0);
        MI_RD                    : in  std_logic;
        MI_WR                    : in  std_logic;
        MI_BE                    : in  std_logic_vector( 3 downto 0);
        MI_DRD                   : out std_logic_vector(31 downto 0);
        MI_ARDY                  : out std_logic;
        MI_DRDY                  : out std_logic;
        -- ===================================================================
        -- ETH DATA interface
        -- ===================================================================
        QSFP_TX_P                : out std_logic_vector(4-1 downto 0);
        QSFP_RX_P                : in  std_logic_vector(4-1 downto 0);
        QSFP_TX_N                : out std_logic_vector(4-1 downto 0);
        QSFP_RX_N                : in  std_logic_vector(4-1 downto 0);
        -- ===================================================================
        -- RX ADAPTER interface
        -- ===================================================================
        -- INPUT MAC SEGMENTED INTERFACE (Intel F-Tile IP)
        RX_MACSI_MAC_DATA        : out std_logic_vector(256-1 downto 0);
        RX_MACSI_MAC_INFRAME     : out std_logic_vector(4-1   downto 0);
        RX_MACSI_MAC_EOP_EMPTY   : out std_logic_vector(12-1  downto 0);
        RX_MACSI_MAC_FCS_ERROR   : out std_logic_vector(4-1   downto 0);
        RX_MACSI_MAC_ERROR       : out std_logic_vector(8-1   downto 0);
        RX_MACSI_MAC_STATUS      : out std_logic_vector(12-1  downto 0);
        RX_MACSI_MAC_VALID       : out std_logic;
        -- ===================================================================
        -- TX ADAPTER interface
        -- ===================================================================
        -- OUTPUT MAC SEGMENTED INTERFACE (Intel F-Tile IP)
        TX_MACSI_ADAPT_DATA      : in  std_logic_vector(256-1 downto 0);
        TX_MACSI_ADAPT_INFRAME   : in  std_logic_vector(4-1   downto 0);
        TX_MACSI_ADAPT_EOP_EMPTY : in  std_logic_vector(12-1  downto 0);
        TX_MACSI_ADAPT_ERROR     : in  std_logic_vector(4-1   downto 0);
        TX_MACSI_ADAPT_VALID     : in  std_logic;
        TX_MACSI_MAC_READY       : out std_logic;
        -- ===================================================================
        -- Netvork_MOD_CONE_ENT interface
        -- ===================================================================
        --different for each ftile (vector)
        CLK_ETH_OUT              : out std_logic;
        RESET_ETH                : in  std_logic;
        -- ===================================================================
        -- ADAPTERS link up
        -- ===================================================================
        RX_LINK_UP               : out std_logic;
        TX_LINK_UP               : out std_logic;
        -- ===================================================================
        -- PLL sigs
        -- ===================================================================
        FTILE_PLL_CLK            : in std_logic;
        FTILE_PLL_REFCLK         : in std_logic
    );
end entity;

architecture FULL of FTILE_MULTIRATE_ETH_2x100G4 is

    component ftile_multirate_eth_1x100g is
    port (
        i_clk_tx                         : in  std_logic                      := 'X';             -- clk
        i_clk_rx                         : in  std_logic                      := 'X';             -- clk
        o_clk_pll                        : out std_logic;                                         -- clk
        o_sys_pll_locked                 : out std_logic;                                         -- o_sys_pll_locked
        i_reconfig_clk                   : in  std_logic                      := 'X';             -- clk
        i_reconfig_reset                 : in  std_logic                      := 'X';             -- reset
        o_tx_serial                      : out std_logic_vector(3 downto 0);                      -- o_tx_serial
        i_rx_serial                      : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_rx_serial
        o_tx_serial_n                    : out std_logic_vector(3 downto 0);                      -- o_tx_serial_n
        i_rx_serial_n                    : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_rx_serial_n
        i_clk_ref                        : in  std_logic                      := 'X';             -- clk
        i_clk_sys                        : in  std_logic                      := 'X';             -- clk
        o_p0_clk_tx_div                  : out std_logic;                                         -- clk
        o_p0_clk_rec_div64               : out std_logic;                                         -- clk
        o_p0_clk_rec_div                 : out std_logic;                                         -- clk
        i_p0_rst_n                       : in  std_logic                      := 'X';             -- reset_n
        i_p0_tx_rst_n                    : in  std_logic                      := 'X';             -- reset_n
        i_p0_rx_rst_n                    : in  std_logic                      := 'X';             -- reset_n
        o_p0_rst_ack_n                   : out std_logic;                                         -- o_rst_ack_n
        o_p0_rx_rst_ack_n                : out std_logic;                                         -- o_rx_rst_ack_n
        o_p0_tx_rst_ack_n                : out std_logic;                                         -- o_rx_rst_ack_n
        o_p0_tx_pll_locked               : out std_logic;                                         -- clk
        o_p0_cdr_lock                    : out std_logic;                                         -- clk
        o_p0_tx_lanes_stable             : out std_logic;                                         -- clk
        o_p0_rx_pcs_ready                : out std_logic;                                         -- clk
        i_p0_tx_pfc                      : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- i_p0_tx_pfc
        o_p0_rx_pfc                      : out std_logic_vector(7 downto 0);                      -- o_p0_rx_pfc
        i_p0_tx_pause                    : in  std_logic                      := 'X';             -- i_p0_tx_pause
        o_p0_rx_pause                    : out std_logic;                                         -- o_p0_rx_pause
        o_p0_rx_block_lock               : out std_logic;                                         -- o_p0_rx_block_lock
        o_p0_rx_am_lock                  : out std_logic;                                         -- o_p0_rx_am_lock
        o_p0_local_fault_status          : out std_logic;                                         -- o_p0_local_fault_status
        o_p0_remote_fault_status         : out std_logic;                                         -- o_p0_remote_fault_status
        i_p0_stats_snapshot              : in  std_logic                      := 'X';             -- i_p0_stats_snapshot
        o_p0_rx_hi_ber                   : out std_logic;                                         -- o_p0_rx_hi_ber
        o_p0_rx_pcs_fully_aligned        : out std_logic;                                         -- o_p0_rx_pcs_fully_aligned
        i_p0_reconfig_eth_addr           : in  std_logic_vector(13 downto 0)  := (others => 'X'); -- address
        i_p0_reconfig_eth_byteenable     : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- byteenable
        o_p0_reconfig_eth_readdata_valid : out std_logic;                                         -- readdatavalid
        i_p0_reconfig_eth_read           : in  std_logic                      := 'X';             -- read
        i_p0_reconfig_eth_write          : in  std_logic                      := 'X';             -- write
        o_p0_reconfig_eth_readdata       : out std_logic_vector(31 downto 0);                     -- readdata
        i_p0_reconfig_eth_writedata      : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- writedata
        o_p0_reconfig_eth_waitrequest    : out std_logic;                                         -- waitrequest
        o_p1_clk_tx_div                  : out std_logic;                                         -- clk
        o_p1_clk_rec_div64               : out std_logic;                                         -- clk
        o_p1_clk_rec_div                 : out std_logic;                                         -- clk
        i_p1_rst_n                       : in  std_logic                      := 'X';             -- reset_n
        i_p1_tx_rst_n                    : in  std_logic                      := 'X';             -- reset_n
        i_p1_rx_rst_n                    : in  std_logic                      := 'X';             -- reset_n
        o_p1_rst_ack_n                   : out std_logic;                                         -- o_rst_ack_n
        o_p1_rx_rst_ack_n                : out std_logic;                                         -- o_tx_rst_ack_n
        o_p1_tx_rst_ack_n                : out std_logic;                                         -- o_rx_rst_ack_n
        o_p1_tx_pll_locked               : out std_logic;                                         -- clk
        o_p1_cdr_lock                    : out std_logic;                                         -- clk
        o_p1_tx_lanes_stable             : out std_logic;                                         -- clk
        o_p1_rx_pcs_ready                : out std_logic;                                         -- clk
        i_p1_tx_pfc                      : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- i_p1_tx_pfc
        o_p1_rx_pfc                      : out std_logic_vector(7 downto 0);                      -- o_p1_rx_pfc
        i_p1_tx_pause                    : in  std_logic                      := 'X';             -- i_p1_tx_pause
        o_p1_rx_pause                    : out std_logic;                                         -- o_p1_rx_pause
        o_p1_rx_block_lock               : out std_logic;                                         -- o_p1_rx_block_lock
        o_p1_rx_am_lock                  : out std_logic;                                         -- o_p1_rx_am_lock
        o_p1_local_fault_status          : out std_logic;                                         -- o_p1_local_fault_status
        o_p1_remote_fault_status         : out std_logic;                                         -- o_p1_remote_fault_status
        i_p1_stats_snapshot              : in  std_logic                      := 'X';             -- i_p1_stats_snapshot
        o_p1_rx_hi_ber                   : out std_logic;                                         -- o_p1_rx_hi_ber
        o_p1_rx_pcs_fully_aligned        : out std_logic;                                         -- o_p1_rx_pcs_fully_aligned
        i_p1_reconfig_eth_addr           : in  std_logic_vector(13 downto 0)  := (others => 'X'); -- address
        i_p1_reconfig_eth_byteenable     : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- byteenable
        o_p1_reconfig_eth_readdata_valid : out std_logic;                                         -- readdatavalid
        i_p1_reconfig_eth_read           : in  std_logic                      := 'X';             -- read
        i_p1_reconfig_eth_write          : in  std_logic                      := 'X';             -- write
        o_p1_reconfig_eth_readdata       : out std_logic_vector(31 downto 0);                     -- readdata
        i_p1_reconfig_eth_writedata      : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- writedata
        o_p1_reconfig_eth_waitrequest    : out std_logic;                                         -- waitrequest
        o_p2_clk_tx_div                  : out std_logic;                                         -- clk
        o_p2_clk_rec_div64               : out std_logic;                                         -- clk
        o_p2_clk_rec_div                 : out std_logic;                                         -- clk
        i_p2_rst_n                       : in  std_logic                      := 'X';             -- reset_n
        i_p2_tx_rst_n                    : in  std_logic                      := 'X';             -- reset_n
        i_p2_rx_rst_n                    : in  std_logic                      := 'X';             -- reset_n
        o_p2_rst_ack_n                   : out std_logic;                                         -- o_rst_ack_n
        o_p2_rx_rst_ack_n                : out std_logic;                                         -- o_tx_rst_ack_n
        o_p2_tx_rst_ack_n                : out std_logic;                                         -- o_rx_rst_ack_n
        o_p2_tx_pll_locked               : out std_logic;                                         -- clk
        o_p2_cdr_lock                    : out std_logic;                                         -- clk
        o_p2_tx_lanes_stable             : out std_logic;                                         -- clk
        o_p2_rx_pcs_ready                : out std_logic;                                         -- clk
        i_p2_tx_pfc                      : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- i_p2_tx_pfc
        o_p2_rx_pfc                      : out std_logic_vector(7 downto 0);                      -- o_p2_rx_pfc
        i_p2_tx_pause                    : in  std_logic                      := 'X';             -- i_p2_tx_pause
        o_p2_rx_pause                    : out std_logic;                                         -- o_p2_rx_pause
        o_p2_rx_block_lock               : out std_logic;                                         -- o_p2_rx_block_lock
        o_p2_rx_am_lock                  : out std_logic;                                         -- o_p2_rx_am_lock
        o_p2_local_fault_status          : out std_logic;                                         -- o_p2_local_fault_status
        o_p2_remote_fault_status         : out std_logic;                                         -- o_p2_remote_fault_status
        i_p2_stats_snapshot              : in  std_logic                      := 'X';             -- i_p2_stats_snapshot
        o_p2_rx_hi_ber                   : out std_logic;                                         -- o_p2_rx_hi_ber
        o_p2_rx_pcs_fully_aligned        : out std_logic;                                         -- o_p2_rx_pcs_fully_aligned
        i_p2_reconfig_eth_addr           : in  std_logic_vector(13 downto 0)  := (others => 'X'); -- address
        i_p2_reconfig_eth_byteenable     : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- byteenable
        o_p2_reconfig_eth_readdata_valid : out std_logic;                                         -- readdatavalid
        i_p2_reconfig_eth_read           : in  std_logic                      := 'X';             -- read
        i_p2_reconfig_eth_write          : in  std_logic                      := 'X';             -- write
        o_p2_reconfig_eth_readdata       : out std_logic_vector(31 downto 0);                     -- readdata
        i_p2_reconfig_eth_writedata      : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- writedata
        o_p2_reconfig_eth_waitrequest    : out std_logic;                                         -- waitrequest
        o_p3_clk_tx_div                  : out std_logic;                                         -- clk
        o_p3_clk_rec_div64               : out std_logic;                                         -- clk
        o_p3_clk_rec_div                 : out std_logic;                                         -- clk
        i_p3_rst_n                       : in  std_logic                      := 'X';             -- reset_n
        i_p3_tx_rst_n                    : in  std_logic                      := 'X';             -- reset_n
        i_p3_rx_rst_n                    : in  std_logic                      := 'X';             -- reset_n
        o_p3_rst_ack_n                   : out std_logic;                                         -- o_rst_ack_n
        o_p3_rx_rst_ack_n                : out std_logic;                                         -- o_tx_rst_ack_n
        o_p3_tx_rst_ack_n                : out std_logic;                                         -- o_rx_rst_ack_n
        o_p3_tx_pll_locked               : out std_logic;                                         -- clk
        o_p3_cdr_lock                    : out std_logic;                                         -- clk
        o_p3_tx_lanes_stable             : out std_logic;                                         -- clk
        o_p3_rx_pcs_ready                : out std_logic;                                         -- clk
        i_p3_tx_pfc                      : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- i_p3_tx_pfc
        o_p3_rx_pfc                      : out std_logic_vector(7 downto 0);                      -- o_p3_rx_pfc
        i_p3_tx_pause                    : in  std_logic                      := 'X';             -- i_p3_tx_pause
        o_p3_rx_pause                    : out std_logic;                                         -- o_p3_rx_pause
        o_p3_rx_block_lock               : out std_logic;                                         -- o_p3_rx_block_lock
        o_p3_rx_am_lock                  : out std_logic;                                         -- o_p3_rx_am_lock
        o_p3_local_fault_status          : out std_logic;                                         -- o_p3_local_fault_status
        o_p3_remote_fault_status         : out std_logic;                                         -- o_p3_remote_fault_status
        i_p3_stats_snapshot              : in  std_logic                      := 'X';             -- i_p3_stats_snapshot
        o_p3_rx_hi_ber                   : out std_logic;                                         -- o_p3_rx_hi_ber
        o_p3_rx_pcs_fully_aligned        : out std_logic;                                         -- o_p3_rx_pcs_fully_aligned
        i_p3_reconfig_eth_addr           : in  std_logic_vector(13 downto 0)  := (others => 'X'); -- address
        i_p3_reconfig_eth_byteenable     : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- byteenable
        o_p3_reconfig_eth_readdata_valid : out std_logic;                                         -- readdatavalid
        i_p3_reconfig_eth_read           : in  std_logic                      := 'X';             -- read
        i_p3_reconfig_eth_write          : in  std_logic                      := 'X';             -- write
        o_p3_reconfig_eth_readdata       : out std_logic_vector(31 downto 0);                     -- readdata
        i_p3_reconfig_eth_writedata      : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- writedata
        o_p3_reconfig_eth_waitrequest    : out std_logic;                                         -- waitrequest
        i_clk_pll                        : in  std_logic                      := 'X';             -- clk
        i_p0_clk_tx_tod                  : in  std_logic                      := 'X';             -- clk
        i_p0_clk_rx_tod                  : in  std_logic                      := 'X';             -- clk
        i_p1_clk_tx_tod                  : in  std_logic                      := 'X';             -- clk
        i_p1_clk_rx_tod                  : in  std_logic                      := 'X';             -- clk
        i_p2_clk_tx_tod                  : in  std_logic                      := 'X';             -- clk
        i_p2_clk_rx_tod                  : in  std_logic                      := 'X';             -- clk
        i_p3_clk_tx_tod                  : in  std_logic                      := 'X';             -- clk
        i_p3_clk_rx_tod                  : in  std_logic                      := 'X';             -- clk
        i_reconfig_xcvr0_addr            : in  std_logic_vector(17 downto 0)  := (others => 'X'); -- address
        i_reconfig_xcvr0_byteenable      : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- byteenable
        o_reconfig_xcvr0_readdata_valid  : out std_logic;                                         -- readdatavalid
        i_reconfig_xcvr0_read            : in  std_logic                      := 'X';             -- read
        i_reconfig_xcvr0_write           : in  std_logic                      := 'X';             -- write
        o_reconfig_xcvr0_readdata        : out std_logic_vector(31 downto 0);                     -- readdata
        i_reconfig_xcvr0_writedata       : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- writedata
        o_reconfig_xcvr0_waitrequest     : out std_logic;                                         -- waitrequest
        i_reconfig_xcvr1_addr            : in  std_logic_vector(17 downto 0)  := (others => 'X'); -- address
        i_reconfig_xcvr1_byteenable      : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- byteenable
        o_reconfig_xcvr1_readdata_valid  : out std_logic;                                         -- readdatavalid
        i_reconfig_xcvr1_read            : in  std_logic                      := 'X';             -- read
        i_reconfig_xcvr1_write           : in  std_logic                      := 'X';             -- write
        o_reconfig_xcvr1_readdata        : out std_logic_vector(31 downto 0);                     -- readdata
        i_reconfig_xcvr1_writedata       : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- writedata
        o_reconfig_xcvr1_waitrequest     : out std_logic;                                         -- waitrequest
        i_reconfig_xcvr2_addr            : in  std_logic_vector(17 downto 0)  := (others => 'X'); -- address
        i_reconfig_xcvr2_byteenable      : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- byteenable
        o_reconfig_xcvr2_readdata_valid  : out std_logic;                                         -- readdatavalid
        i_reconfig_xcvr2_read            : in  std_logic                      := 'X';             -- read
        i_reconfig_xcvr2_write           : in  std_logic                      := 'X';             -- write
        o_reconfig_xcvr2_readdata        : out std_logic_vector(31 downto 0);                     -- readdata
        i_reconfig_xcvr2_writedata       : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- writedata
        o_reconfig_xcvr2_waitrequest     : out std_logic;                                         -- waitrequest
        i_reconfig_xcvr3_addr            : in  std_logic_vector(17 downto 0)  := (others => 'X'); -- address
        i_reconfig_xcvr3_byteenable      : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- byteenable
        o_reconfig_xcvr3_readdata_valid  : out std_logic;                                         -- readdatavalid
        i_reconfig_xcvr3_read            : in  std_logic                      := 'X';             -- read
        i_reconfig_xcvr3_write           : in  std_logic                      := 'X';             -- write
        o_reconfig_xcvr3_readdata        : out std_logic_vector(31 downto 0);                     -- readdata
        i_reconfig_xcvr3_writedata       : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- writedata
        o_reconfig_xcvr3_waitrequest     : out std_logic;                                         -- waitrequest
        i_tx_mac_data                    : in  std_logic_vector(255 downto 0) := (others => 'X'); -- i_tx_mac_data
        i_tx_mac_valid                   : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_tx_mac_valid
        i_tx_mac_inframe                 : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_tx_mac_inframe
        i_tx_mac_eop_empty               : in  std_logic_vector(11 downto 0)  := (others => 'X'); -- i_tx_mac_eop_empty
        o_tx_mac_ready                   : out std_logic_vector(3 downto 0);                      -- o_tx_mac_ready
        i_tx_mac_error                   : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_tx_mac_error
        i_tx_mac_skip_crc                : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- i_tx_mac_skip_crc
        o_rx_mac_data                    : out std_logic_vector(255 downto 0);                    -- o_rx_mac_data
        o_rx_mac_valid                   : out std_logic_vector(3 downto 0);                      -- o_rx_mac_valid
        o_rx_mac_inframe                 : out std_logic_vector(3 downto 0);                      -- o_rx_mac_inframe
        o_rx_mac_eop_empty               : out std_logic_vector(11 downto 0);                     -- o_rx_mac_eop_empty
        o_rx_mac_fcs_error               : out std_logic_vector(3 downto 0);                      -- o_rx_mac_fcs_error
        o_rx_mac_error                   : out std_logic_vector(7 downto 0);                      -- o_rx_mac_error
        o_rx_mac_status                  : out std_logic_vector(11 downto 0)                      -- o_rx_mac_status
    );
    end component ftile_multirate_eth_1x100g;

    -- Dynamic reconfiguration controller for the multirate IP 
    component dr_ctrl is
    port (
        i_csr_clk                     : in  std_logic                     := 'X';             -- clk
        i_cpu_clk                     : in  std_logic                     := 'X';             -- clk
        i_rst_n                       : in  std_logic                     := 'X';             -- reset_n
        o_dr_curr_profile_id          : out std_logic_vector(14 downto 0);                    -- o_dr_curr_profile_id
        o_dr_new_cfg_applied          : out std_logic;                                        -- o_dr_new_cfg_applied
        i_dr_new_cfg_applied_ack      : in  std_logic                     := 'X';             -- i_dr_new_cfg_applied_ack
        o_dr_in_progress              : out std_logic;                                        -- o_dr_in_progress
        o_dr_error_status             : out std_logic;                                        -- o_dr_error_status
        i_dr_host_avmm_address        : in  std_logic_vector(9 downto 0)  := (others => 'X'); -- address
        o_dr_host_avmm_readdata_valid : out std_logic;                                        -- readdatavalid
        i_dr_host_avmm_read           : in  std_logic                     := 'X';             -- read
        i_dr_host_avmm_write          : in  std_logic                     := 'X';             -- write
        o_dr_host_avmm_readdata       : out std_logic_vector(31 downto 0);                    -- readdata
        i_dr_host_avmm_writedata      : in  std_logic_vector(31 downto 0) := (others => 'X'); -- writedata
        o_dr_host_avmm_waitrequest    : out std_logic                                         -- waitrequest
    );
    end component dr_ctrl;

    -- Select the usage of DR_CTRL for channel (0)
    function mi_en_map_stat return natural is
    begin
        case IP_CNT is
            when 0      => return 2079; -- represent IP(0) which include dr_ctrl
            when others => return 31;   -- represent others IPs without dr_ctrl (only one needed for all IP cores)
        end case;
    end function;

    function mi_en_map_null return natural is
    begin
        case IP_CNT is
            when 0      => return 1; -- represent IP(0) where reconfig_bus(11) from bridgge_drp is used
            when others => return 0; -- represent IPs other then IP(0) where reconfig_bus(11) from bridgge_drp isn't used
        end case;
    end function;

    -- ===================================================================
    -- Constants
    -- ===================================================================
    -- constants for IP core setup
    constant NUM_LANES     : natural   :=  20;
    constant PMA_LANES     : natural   :=   4;
    constant ETH_PORT_CHAN : natural   :=   1;
    constant SPEED         : natural   := 100;
    constant SPEED_CAP     : std_logic_vector(15 downto 0) :=  X"0200";
    constant DEVICE        : string    :=  "AGILEX";
    constant RSFEC_ABLE    : std_logic := '0';
    constant AN_ABLE       : std_logic := '0';

    -- bridge vector lenght constant
    constant MI_SEL_RANGE : natural := 16;

    -- Adress and data range constants for eth and xcvr
    constant MI_ADDR_WIDTH_PHY : natural := 32;
    constant MI_DATA_WIDTH_PHY : natural := 32;

    --  monitoring RX link state
    constant RX_LINK_CNT_W : natural := 27;

    -- constant for segments for macseg_loop size
    constant SEGMENTS_LOOP : natural := 4;

    -- constants for mac data for TX/RX
    constant MAC_DATA_WIDTH      : natural := 256;
    constant MAC_INFRAME_WIDHT   : natural :=   4;
    constant MAC_EOP_EMPTY_WIDTH : natural :=  12;
    constant MAC_ERROR_TX_WIDTH  : natural :=   4;
    constant MAC_FCS_ERROR_WIDTH : natural :=   4;
    constant MAC_ERROR_RX_WIDTH  : natural :=   8;
    constant MAC_STATUS_WIDTH    : natural :=  12;

    -- signals for mgmt => mi_sel interface
    signal drpdo    : std_logic_vector(MI_DATA_WIDTH_PHY-1 downto 0);
    signal drp_drdy : std_logic;
    signal drpen    : std_logic;
    signal drpwe    : std_logic;
    signal drpaddr  : std_logic_vector(MI_ADDR_WIDTH_PHY-1 downto 0);
    signal drpardy  : std_logic;
    signal drpdi    : std_logic_vector(MI_DATA_WIDTH_PHY-1 downto 0);
    signal drpsel   : std_logic_vector(4-1 downto 0);

    -- signals for mi_sel => IP core interface
    signal reconfig_addr           :  slv_array_t     (MI_SEL_RANGE-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    signal reconfig_readdata_valid :  std_logic_vector(MI_SEL_RANGE-1 downto 0);
    signal reconfig_read           :  std_logic_vector(MI_SEL_RANGE-1 downto 0);
    signal reconfig_write          :  std_logic_vector(MI_SEL_RANGE-1 downto 0);
    signal reconfig_readdata       :  slv_array_t     (MI_SEL_RANGE-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal reconfig_writedata      :  slv_array_t     (MI_SEL_RANGE-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal reconfig_waitrequest    :  std_logic_vector(MI_SEL_RANGE-1 downto 0);

    -- signals for multiplexor
    signal reconfig_write_drp      :  std_logic_vector(MI_SEL_RANGE-1 downto 0);
    signal reconfig_read_drp       :  std_logic_vector(MI_SEL_RANGE-1 downto 0);
    signal reconfig_addr_drp       :  slv_array_t     (MI_SEL_RANGE-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    signal reconfig_writedata_drp  :  slv_array_t     (MI_SEL_RANGE-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);

    -- signal for Ftile interface
    signal ftile_rx_rst_n             : std_logic;
    signal ftile_rx_rst_ack_n         : std_logic;
    signal ftile_tx_lanes_stable      : std_logic;
    signal ftile_rx_pcs_ready         : std_logic;
    -- signal ftile_pll_refclk           : std_logic;
    signal ftile_rx_block_lock        : std_logic;
    signal ftile_rx_am_lock           : std_logic;
    signal ftile_local_fault          : std_logic; -- not used
    signal ftile_remote_fault         : std_logic;
    signal ftile_rx_hi_ber            : std_logic;
    signal ftile_rx_pcs_fully_aligned : std_logic;

    -- signals for sync repeater
    signal ftile_tx_loop_data      : std_logic_vector(MAC_DATA_WIDTH      -1 downto 0);
    signal ftile_tx_loop_valid     : std_logic;
    signal ftile_tx_loop_inframe   : std_logic_vector(MAC_INFRAME_WIDHT   -1 downto 0);
    signal ftile_tx_loop_eop_empty : std_logic_vector(MAC_EOP_EMPTY_WIDTH -1 downto 0);
    signal ftile_tx_loop_ready     : std_logic;
    signal ftile_tx_loop_error     : std_logic_vector(MAC_ERROR_TX_WIDTH  -1 downto 0);

    -- multiplexor output conected to mac input of IP core
    signal ftile_tx_mac_data       : std_logic_vector(MAC_DATA_WIDTH      -1 downto 0);
    signal ftile_tx_mac_valid      : std_logic;
    signal ftile_tx_mac_inframe    : std_logic_vector(MAC_INFRAME_WIDHT   -1 downto 0);
    signal ftile_tx_mac_eop_empty  : std_logic_vector(MAC_EOP_EMPTY_WIDTH -1 downto 0);
    signal ftile_tx_mac_ready      : std_logic;
    signal ftile_tx_mac_error      : std_logic_vector(MAC_ERROR_TX_WIDTH  -1 downto 0);

    -- For QuestaSim
    signal ftile_tx_mac_ready_dummy : std_logic_vector(4-1 downto 0);

    -- signals from mac output of IP core to Component Out
    signal ftile_rx_mac_data       : std_logic_vector(MAC_DATA_WIDTH      -1 downto 0);
    signal ftile_rx_mac_valid      : std_logic;
    signal ftile_rx_mac_inframe    : std_logic_vector(MAC_INFRAME_WIDHT   -1 downto 0);
    signal ftile_rx_mac_eop_empty  : std_logic_vector(MAC_EOP_EMPTY_WIDTH -1 downto 0);
    signal ftile_rx_mac_fcs_error  : std_logic_vector(MAC_FCS_ERROR_WIDTH -1 downto 0);
    signal ftile_rx_mac_error      : std_logic_vector(MAC_ERROR_RX_WIDTH  -1 downto 0);
    signal ftile_rx_mac_status     : std_logic_vector(MAC_STATUS_WIDTH    -1 downto 0);

    -- For QuestaSim
    signal ftile_rx_mac_valid_dummy : std_logic_vector(4-1 downto 0);

    signal mgmt_pcs_reset   : std_logic; -- not used
    signal mgmt_pma_reset   : std_logic;
    signal mgmt_mac_loop    : std_logic;
    signal mgmt_pcs_control : std_logic_vector(16-1 downto 0);
    signal mgmt_pcs_status  : std_logic_vector(16-1 downto 0);

    -- For QuestaSim
    signal mgmt_pcs_control_dummy : std_logic_vector(15-1 downto 0);

    -- Synchronization of REPEATER_CTRL
    -- signal sync_repeater_ctrl : std_logic_vector(REPEATER_CTRL'range);
    signal sync_repeater_ctrl : std_logic;

    signal reconfig_waitrequest_drp : std_logic_vector(MI_SEL_RANGE-1 downto 0) := (others => '0');
    signal init_done      : std_logic_vector(PMA_LANES   -1 downto 0);
    signal init_ready     : std_logic_vector(PMA_LANES   -1 downto 0);

    signal rx_link_cnt    : unsigned(RX_LINK_CNT_W-1 downto 0);
    signal rx_link_rst    : std_logic;

    signal ftile_clk_out  : std_logic;

begin
    mgmt_i : entity work.mgmt
    generic map (
        NUM_LANES  => NUM_LANES,
        PMA_LANES  => PMA_LANES,
        SPEED      => SPEED,
        SPEED_CAP  => SPEED_CAP,
        DEVICE     => DEVICE,
        RSFEC_ABLE => RSFEC_ABLE,
        AN_ABLE    => AN_ABLE,
        DRP_DWIDTH => MI_DATA_WIDTH_PHY,
        DRP_AWIDTH => MI_ADDR_WIDTH_PHY
    )
    port map (
        RESET                    => MI_RESET_PHY,
        MI_CLK                   => MI_CLK_PHY,
        MI_DWR                   => MI_DWR,
        MI_ADDR                  => MI_ADDR,
        MI_RD                    => MI_RD,
        MI_WR                    => MI_WR,
        MI_BE                    => MI_BE,
        MI_DRD                   => MI_DRD,
        MI_ARDY                  => MI_ARDY,
        MI_DRDY                  => MI_DRDY,
        -- PCS status
        HI_BER                   => ftile_rx_hi_ber,
        BLK_LOCK                 => (others => ftile_rx_block_lock),
        LINKSTATUS               => ftile_rx_pcs_fully_aligned and not ftile_rx_hi_ber,
        BER_COUNT                => (others => '0'),
        BER_COUNT_CLR            => open,
        BLK_ERR_CNTR             => (others => '0'),
        BLK_ERR_CLR              => open,
        SCR_BYPASS               => open,
        PCS_RESET                => mgmt_pcs_reset, --TODO 
        PCS_LPBCK                => open,
        PCS_CONTROL(0)           => mgmt_mac_loop,
        PCS_CONTROL(15 downto 1) => mgmt_pcs_control_dummy,
        PCS_CONTROL_I            => mgmt_pcs_control,
        PCS_STATUS               => mgmt_pcs_status,
        -- PCS Lane align
        ALGN_LOCKED              => ftile_rx_am_lock,
        BIP_ERR_CNTRS            => (others => '0'),
        BIP_ERR_CLR              => open,
        LANE_MAP                 => (others => '0'),
        LANE_ALIGN               => (others => ftile_rx_pcs_fully_aligned),
        -- PMA & PMD status/control
        PMA_LOPWR                => open,
        PMA_LPBCK                => open,
        PMA_REM_LPBCK            => open,
        PMA_RESET                => mgmt_pma_reset, --TODO 
        PMA_RETUNE               => open,
        PMA_CONTROL              => open,
        PMA_STATUS               => (others => '0'),
        PMA_PTRN_EN              => open,
        PMA_TX_DIS               => open,
        PMA_RX_OK                => (others => ftile_rx_pcs_ready), --TODO
        PMD_SIG_DET              => (others => ftile_rx_pcs_ready), --TODO
        PMA_PRECURSOR            => open,
        PMA_POSTCURSOR           => open,
        PMA_DRIVE                => open,
        -- Dynamic reconfiguration interface
        DRPCLK                   => MI_CLK_PHY,
        DRPDO                    => drpdo,
        DRPRDY                   => drp_drdy, -- DRDY is set during JTAG operations, therefore using ia_rd as mask
        DRPEN                    => drpen,
        DRPWE                    => drpwe,
        DRPADDR                  => drpaddr,
        DRPARDY                  => drpardy,
        DRPDI                    => drpdi,
        DRPSEL                   => drpsel
    );

    -- MDIO reg 3.4000 (vendor specific PCS control readout)
    mgmt_pcs_control(15 downto 1) <= (others => '0');
    mgmt_pcs_control(0)           <= sync_repeater_ctrl; -- MAC loopback active
    -- MDIO reg 3.4001 (vendor specific PCS status/abilities)
    mgmt_pcs_status(15 downto 1) <= (others => '0'); 
    mgmt_pcs_status(0)           <= '1';        -- MAC loopback ability supported

    drp_bridge_i : entity work.bridge_drp
    generic map (
        MI_DATA_WIDTH_PHY => MI_DATA_WIDTH_PHY,
        MI_ADDR_WIDTH_PHY => MI_ADDR_WIDTH_PHY,
        MI_SEL_RANGE      => MI_SEL_RANGE,
        MI_EN_MAP         => std_logic_vector(to_unsigned(mi_en_map_stat,MI_SEL_RANGE))
    )
    port map (
        DRPCLK                  => MI_CLK_PHY,
        DRPDO                   => drpdo,
        DRP_DRDY                => drp_drdy,
        DRPEN                   => drpen,
        DRPWE                   => drpwe,
        DRPADDR                 => drpaddr,
        DRPARDY                 => drpardy,
        DRPDI                   => drpdi,
        DRPSEL                  => drpsel,

        RECONFIG_ADDR           => reconfig_addr_drp,
        RECONFIG_READDATA_VALID => reconfig_readdata_valid,
        RECONFIG_READ           => reconfig_read_drp,
        RECONFIG_WRITE          => reconfig_write_drp,
        RECONFIG_READDATA       => reconfig_readdata,
        RECONFIG_WRITEDATA      => reconfig_writedata_drp,
        RECONFIG_WAITREQUEST    => reconfig_waitrequest_drp
    );

    -- selection of unused input signals from bridge_drp which have to be conect to '0'
    -- if IP is IP(0) then range is from            (16:12) & (10:5)
    -- if IP is other than IP(0) then range is from (16:11) & (10:5)
    reconfig_readdata_valid (MI_SEL_RANGE-1 downto 11 + mi_en_map_null) <= (others => '0');
    reconfig_readdata_valid (10             downto PMA_LANES+1)         <= (others => '0');
    reconfig_waitrequest    (MI_SEL_RANGE-1 downto 11 + mi_en_map_null) <= (others => '0');
    reconfig_waitrequest    (10             downto PMA_LANES+1)         <= (others => '0');
    reconfig_readdata       (MI_SEL_RANGE-1 downto 11 + mi_en_map_null) <= (others => (others => '0'));
    reconfig_readdata       (10             downto PMA_LANES+1)         <= (others => (others => '0'));

    -- monitoring RX link state
    process(ftile_clk_out)
    begin
        if rising_edge(ftile_clk_out) then
            if (ftile_rx_pcs_ready = '1') or (rx_link_rst = '1') then
                -- link is up, clear the counter
                rx_link_cnt <= (others => '0');
            else
                -- link is down, increase the counter
                rx_link_cnt <= rx_link_cnt + 1;
            end if;

            -- when its last bit (~100ms) is set, reset the link
            if (rx_link_cnt(RX_LINK_CNT_W-1) = '1') then
                rx_link_rst <= '1';
            elsif (ftile_rx_rst_ack_n = '0' and rx_link_rst = '1') then
                rx_link_rst <= '0';
            end if;

            if (RESET_ETH = '1') then
                rx_link_cnt <= (others => '0');
                rx_link_rst <= '0';
            end if;
        end if;
    end process;

    ftile_rx_rst_n <= not rx_link_rst;

    xcvr_reconfig_inf_res_g: for xcvr in PMA_LANES-1 downto 0 generate

        constant IA_INDEX : natural := 1 + xcvr;

        signal init_busy      : std_logic;
        signal init_addr      : std_logic_vector(17 downto 0);
        signal init_read      : std_logic;
        signal init_write     : std_logic;
        signal init_writedata : std_logic_vector(31 downto 0);

    begin

        -- Generate AVMM signals for XCVR blocks
        reconfig_write  (IA_INDEX) <=
            init_write                   when init_busy = '1'                                      else
            reconfig_write_drp(IA_INDEX) when drpsel = std_logic_vector(to_unsigned(xcvr+1,4))     else
            '0';
        reconfig_read  (IA_INDEX) <=
            init_read                    when init_busy = '1'                                     else
            reconfig_read_drp (IA_INDEX) when drpsel = std_logic_vector(to_unsigned(xcvr+1,4))    else
            '0';
        reconfig_addr(IA_INDEX) <=
             X"000" & "00" & init_addr   when init_busy = '1'  else
             reconfig_addr_drp(IA_INDEX)(reconfig_addr(0)'range);
        reconfig_writedata (IA_INDEX) <=
            init_writedata                when init_busy = '1'  else
            reconfig_writedata_drp (IA_INDEX);
            
        init_done_g: if (xcvr = 0) generate
            init_ready(0) <= ftile_tx_lanes_stable;
        else generate
            init_ready(xcvr) <= init_done(xcvr-1);
        end generate;

        -- Component ftile_xcvr_init perform set_media_mode() operation to bring the link up on optical media types
        xcvr_init: entity work.ftile_xcvr_init
        generic map (
            PHY_LANE => (3 - (xcvr mod 4)) -- XCVR 0 maps to -> PHY lane 3, XCVR1 -> 2, XCVR2 -> 1 and XCVR3 -> 0
        )
        port map (
            RST              => RESET_ETH or mgmt_pma_reset,
            XCVR_RDY         => init_ready(xcvr),
            CLK              => MI_CLK_PHY,
            ROM_SEL          => "0", -- 0 means optical mode configuration, 1 means CR mode configuration
            BUSY             => init_busy,
            DONE             => init_done(xcvr),
            -- AVMM
            ADDRESS          => init_addr,
            READ             => init_read,
            WRITE            => init_write,
            READDATA         => reconfig_readdata(IA_INDEX),
            READDATA_VALID   => reconfig_readdata_valid(IA_INDEX),
            WRITEDATA        => init_writedata,
            WAITREQUEST      => reconfig_waitrequest(IA_INDEX),
            STATE            => open -- debug purposes only. Can be left open in the future
         );

    end generate;

    mi_ardy_conversion_g: for i in PMA_LANES downto 0 generate
        reconfig_waitrequest_drp(i) <= not reconfig_waitrequest(i);
    end generate;

    CLK_ETH_OUT <= ftile_clk_out;
    -- =========================================================================
    -- DR_CTRL
    -- =========================================================================
    -- can't have more than 1 IP component in whole design (1 DR_CTRL for all F-Tile Multirate IP cores)
    dr_ctrl_g : if IP_CNT = 0 generate
        dr_ctrl_i : component dr_ctrl
        port map (
            i_csr_clk                     => MI_CLK_PHY,
            i_cpu_clk                     => MI_CLK_PHY,
            i_rst_n                       => not MI_RESET_PHY,
            o_dr_curr_profile_id          => open,
            o_dr_new_cfg_applied          => open,
            i_dr_new_cfg_applied_ack      => '1',
            o_dr_in_progress              => open,
            o_dr_error_status             => open,
            i_dr_host_avmm_address        => reconfig_addr_drp        (11)(10-1 downto 0),
            o_dr_host_avmm_readdata_valid => reconfig_readdata_valid  (11),
            i_dr_host_avmm_read           => reconfig_read_drp        (11),
            i_dr_host_avmm_write          => reconfig_write_drp       (11),
            o_dr_host_avmm_readdata       => reconfig_readdata        (11),
            i_dr_host_avmm_writedata      => reconfig_writedata_drp   (11),
            o_dr_host_avmm_waitrequest    => reconfig_waitrequest_drp (11)
        );
    end generate dr_ctrl_g;

    -- =========================================================================
    -- F-TILE Ethernet
    -- =========================================================================
    -- can't have more than 8 100g lines devided into 2 channels
    ftile_eth_ip_i : component ftile_multirate_eth_1x100g
    port map (
        i_clk_tx                         => ftile_clk_out,
        i_clk_rx                         => ftile_clk_out,
        o_clk_pll                        => ftile_clk_out,
        o_sys_pll_locked                 => open,
        i_reconfig_clk                   => MI_CLK_PHY,
        i_reconfig_reset                 => MI_RESET_PHY,
        o_tx_serial                      => QSFP_TX_P,
        i_rx_serial                      => QSFP_RX_P,
        o_tx_serial_n                    => QSFP_TX_N,
        i_rx_serial_n                    => QSFP_RX_N,
        i_clk_ref                        => FTILE_PLL_REFCLK,
        i_clk_sys                        => FTILE_PLL_CLK,
        -- ========
        -- |Port 0|
        -- ========
        o_p0_clk_tx_div                  => open,
        o_p0_clk_rec_div64               => open,
        o_p0_clk_rec_div                 => open,
        i_p0_rst_n                       => not RESET_ETH,
        i_p0_tx_rst_n                    => '1',
        i_p0_rx_rst_n                    => ftile_rx_rst_n,
        o_p0_rst_ack_n                   => open,
        o_p0_rx_rst_ack_n                => ftile_rx_rst_ack_n,
        o_p0_tx_rst_ack_n                => open,
        o_p0_tx_pll_locked               => open,
        o_p0_cdr_lock                    => open,
        o_p0_tx_lanes_stable             => ftile_tx_lanes_stable,
        o_p0_rx_pcs_ready                => ftile_rx_pcs_ready,
        i_p0_tx_pfc                      => (others => '0'),
        o_p0_rx_pfc                      => open,
        i_p0_tx_pause                    => '0',
        o_p0_rx_pause                    => open,
        o_p0_rx_block_lock               => ftile_rx_block_lock,
        o_p0_rx_am_lock                  => ftile_rx_am_lock,
        o_p0_local_fault_status          => ftile_local_fault,
        o_p0_remote_fault_status         => ftile_remote_fault,
        i_p0_stats_snapshot              => '0',
        o_p0_rx_hi_ber                   => ftile_rx_hi_ber,
        o_p0_rx_pcs_fully_aligned        => ftile_rx_pcs_fully_aligned,
        -- ethernet reconfig port(0) (+ RSFEC + Transciever) reconfig inf 0x0 for each channel
        i_p0_reconfig_eth_addr           => reconfig_addr_drp       (0)(14-1 downto 0),
        i_p0_reconfig_eth_byteenable     => (others => '1')            , -- not supported in MI IA yet
        o_p0_reconfig_eth_readdata_valid => reconfig_readdata_valid (0),
        i_p0_reconfig_eth_read           => reconfig_read_drp       (0),
        i_p0_reconfig_eth_write          => reconfig_write_drp      (0),
        o_p0_reconfig_eth_readdata       => reconfig_readdata       (0),
        i_p0_reconfig_eth_writedata      => reconfig_writedata_drp  (0),
        o_p0_reconfig_eth_waitrequest    => reconfig_waitrequest    (0),
        -- ========
        -- |Port 1|
        -- ========
        o_p1_clk_tx_div                     => open           ,
        o_p1_clk_rec_div64                  => open           ,
        o_p1_clk_rec_div                    => open           ,
        i_p1_rst_n                          => '1'            ,
        i_p1_tx_rst_n                       => '1'            ,
        i_p1_rx_rst_n                       => '1'            ,
        o_p1_rst_ack_n                      => open           ,
        o_p1_rx_rst_ack_n                   => open           ,
        o_p1_tx_rst_ack_n                   => open           ,
        o_p1_tx_pll_locked                  => open           ,
        o_p1_cdr_lock                       => open           ,
        o_p1_tx_lanes_stable                => open           ,
        o_p1_rx_pcs_ready                   => open           ,
        i_p1_tx_pfc                         => (others => '0'),
        o_p1_rx_pfc                         => open           ,
        i_p1_tx_pause                       => '0'            ,
        o_p1_rx_pause                       => open           ,
        o_p1_rx_block_lock                  => open           ,
        o_p1_rx_am_lock                     => open           ,
        o_p1_local_fault_status             => open           ,
        o_p1_remote_fault_status            => open           ,
        i_p1_stats_snapshot                 => '0'            ,
        o_p1_rx_hi_ber                      => open           ,
        o_p1_rx_pcs_fully_aligned           => open           ,
        -- ethernet reconfig port(1)
        i_p1_reconfig_eth_addr              => (others => '0'),
        i_p1_reconfig_eth_byteenable        => (others => '1'),
        o_p1_reconfig_eth_readdata_valid    => open           ,
        i_p1_reconfig_eth_read              => '0'            ,
        i_p1_reconfig_eth_write             => '0'            ,
        o_p1_reconfig_eth_readdata          => open           ,
        i_p1_reconfig_eth_writedata         => (others => '0'),
        o_p1_reconfig_eth_waitrequest       => open           ,
        -- ========
        -- |Port 2|
        -- ========
        o_p2_clk_tx_div                     => open           ,
        o_p2_clk_rec_div64                  => open           ,
        o_p2_clk_rec_div                    => open           ,
        i_p2_rst_n                          => '1'            ,
        i_p2_tx_rst_n                       => '1'            ,
        i_p2_rx_rst_n                       => '1'            ,
        o_p2_rst_ack_n                      => open           ,
        o_p2_rx_rst_ack_n                   => open           ,
        o_p2_tx_rst_ack_n                   => open           ,
        o_p2_tx_pll_locked                  => open           ,
        o_p2_cdr_lock                       => open           ,
        o_p2_tx_lanes_stable                => open           ,
        o_p2_rx_pcs_ready                   => open           ,
        i_p2_tx_pfc                         => (others => '0'),
        o_p2_rx_pfc                         => open           ,
        i_p2_tx_pause                       => '0'            ,
        o_p2_rx_pause                       => open           ,
        o_p2_rx_block_lock                  => open           ,
        o_p2_rx_am_lock                     => open           ,
        o_p2_local_fault_status             => open           ,
        o_p2_remote_fault_status            => open           ,
        i_p2_stats_snapshot                 => '0'            ,
        o_p2_rx_hi_ber                      => open           ,
        o_p2_rx_pcs_fully_aligned           => open           ,
        -- ethernet reconfig port(2)
        i_p2_reconfig_eth_addr              => (others => '0'),
        i_p2_reconfig_eth_byteenable        => (others => '1'),
        o_p2_reconfig_eth_readdata_valid    => open           ,
        i_p2_reconfig_eth_read              => '0'            ,
        i_p2_reconfig_eth_write             => '0'            ,
        o_p2_reconfig_eth_readdata          => open           ,
        i_p2_reconfig_eth_writedata         => (others => '0'),
        o_p2_reconfig_eth_waitrequest       => open           ,
        -- ========
        -- |Port 3|
        -- ========
        o_p3_clk_tx_div                     => open           ,
        o_p3_clk_rec_div64                  => open           ,
        o_p3_clk_rec_div                    => open           ,
        i_p3_rst_n                          => '1'            ,
        i_p3_tx_rst_n                       => '1'            ,
        i_p3_rx_rst_n                       => '1'            ,
        o_p3_rst_ack_n                      => open           ,
        o_p3_rx_rst_ack_n                   => open           ,
        o_p3_tx_rst_ack_n                   => open           ,
        o_p3_tx_pll_locked                  => open           ,
        o_p3_cdr_lock                       => open           ,
        o_p3_tx_lanes_stable                => open           ,
        o_p3_rx_pcs_ready                   => open           ,
        i_p3_tx_pfc                         => (others => '0'),
        o_p3_rx_pfc                         => open           ,
        i_p3_tx_pause                       => '0'            ,
        o_p3_rx_pause                       => open           ,
        o_p3_rx_block_lock                  => open           ,
        o_p3_rx_am_lock                     => open           ,
        o_p3_local_fault_status             => open           ,
        o_p3_remote_fault_status            => open           ,
        i_p3_stats_snapshot                 => '0'            ,
        o_p3_rx_hi_ber                      => open           ,
        o_p3_rx_pcs_fully_aligned           => open           ,
        -- ethernet reconfig port(3)
        i_p3_reconfig_eth_addr              => (others => '0'),
        i_p3_reconfig_eth_byteenable        => (others => '1'),
        o_p3_reconfig_eth_readdata_valid    => open           ,
        i_p3_reconfig_eth_read              => '0'            ,
        i_p3_reconfig_eth_write             => '0'            ,
        o_p3_reconfig_eth_readdata          => open           ,
        i_p3_reconfig_eth_writedata         => (others => '0'),
        o_p3_reconfig_eth_waitrequest       => open           ,
        -- ====================================================
        --		    | PTP PROTOCOL SETUP CLK |
        -- ====================================================
        i_clk_pll          => '0',
        i_p0_clk_tx_tod    => '0',
        i_p0_clk_rx_tod    => '0',
        i_p1_clk_tx_tod    => '0',
        i_p1_clk_rx_tod    => '0',
        i_p2_clk_tx_tod    => '0',
        i_p2_clk_rx_tod    => '0',
        i_p3_clk_tx_tod    => '0',
        i_p3_clk_rx_tod    => '0',
        -- XCVR reconfig inf (0x1)
        i_reconfig_xcvr0_addr            => reconfig_addr           (1)(18-1 downto 0),
        i_reconfig_xcvr0_byteenable      => (others => '1')            ,
        o_reconfig_xcvr0_readdata_valid  => reconfig_readdata_valid (1),
        i_reconfig_xcvr0_read            => reconfig_read           (1),
        i_reconfig_xcvr0_write           => reconfig_write          (1),
        o_reconfig_xcvr0_readdata        => reconfig_readdata       (1),
        i_reconfig_xcvr0_writedata       => reconfig_writedata      (1),
        o_reconfig_xcvr0_waitrequest     => reconfig_waitrequest    (1),
        -- XCVR reconfig inf (0x2)
        i_reconfig_xcvr1_addr            => reconfig_addr           (2)(18-1 downto 0),
        i_reconfig_xcvr1_byteenable      => (others => '1')            ,
        o_reconfig_xcvr1_readdata_valid  => reconfig_readdata_valid (2),
        i_reconfig_xcvr1_read            => reconfig_read           (2),
        i_reconfig_xcvr1_write           => reconfig_write          (2),
        o_reconfig_xcvr1_readdata        => reconfig_readdata       (2),
        i_reconfig_xcvr1_writedata       => reconfig_writedata      (2),
        o_reconfig_xcvr1_waitrequest     => reconfig_waitrequest    (2),
        -- XCVR reconfig inf (0x3)
        i_reconfig_xcvr2_addr            => reconfig_addr           (3)(18-1 downto 0),
        i_reconfig_xcvr2_byteenable      => (others => '1')            ,
        o_reconfig_xcvr2_readdata_valid  => reconfig_readdata_valid (3),
        i_reconfig_xcvr2_read            => reconfig_read           (3),
        i_reconfig_xcvr2_write           => reconfig_write          (3),
        o_reconfig_xcvr2_readdata        => reconfig_readdata       (3),
        i_reconfig_xcvr2_writedata       => reconfig_writedata      (3),
        o_reconfig_xcvr2_waitrequest     => reconfig_waitrequest    (3),
        -- XCVR reconfig inf (0x4)
        i_reconfig_xcvr3_addr            => reconfig_addr           (4)(18-1 downto 0),
        i_reconfig_xcvr3_byteenable      => (others => '1')            ,
        o_reconfig_xcvr3_readdata_valid  => reconfig_readdata_valid (4),
        i_reconfig_xcvr3_read            => reconfig_read           (4),
        i_reconfig_xcvr3_write           => reconfig_write          (4),
        o_reconfig_xcvr3_readdata        => reconfig_readdata       (4),
        i_reconfig_xcvr3_writedata       => reconfig_writedata      (4),
        o_reconfig_xcvr3_waitrequest     => reconfig_waitrequest    (4),
        -- MAC Status sigs
        i_tx_mac_data                    => ftile_tx_mac_data,
        i_tx_mac_valid(0)                => ftile_tx_mac_valid,
        i_tx_mac_valid(3 downto 1)       => (others => '1'),   -- not used
        i_tx_mac_inframe                 => ftile_tx_mac_inframe,
        i_tx_mac_eop_empty               => ftile_tx_mac_eop_empty,
        o_tx_mac_ready(0)                => ftile_tx_mac_ready,
        o_tx_mac_ready(3 downto 1)       => ftile_tx_mac_ready_dummy, -- not used
        i_tx_mac_error                   => ftile_tx_mac_error,
        i_tx_mac_skip_crc                => (others => '0' ),
        o_rx_mac_data                    => ftile_rx_mac_data,
        o_rx_mac_valid(0)                => ftile_rx_mac_valid,
        o_rx_mac_valid(3 downto 1)       => ftile_rx_mac_valid_dummy, -- not used
        o_rx_mac_inframe                 => ftile_rx_mac_inframe,
        o_rx_mac_eop_empty               => ftile_rx_mac_eop_empty,
        o_rx_mac_fcs_error               => ftile_rx_mac_fcs_error,
        o_rx_mac_error                   => ftile_rx_mac_error,
        o_rx_mac_status                  => ftile_rx_mac_status
    );

    -- TX interface conected to Component Output
    TX_MACSI_MAC_READY     <= ftile_tx_mac_ready;

    -- RX interface conected to Component Output
    RX_MACSI_MAC_DATA      <= ftile_rx_mac_data;
    RX_MACSI_MAC_VALID     <= ftile_rx_mac_valid;
    RX_MACSI_MAC_INFRAME   <= ftile_rx_mac_inframe;
    RX_MACSI_MAC_EOP_EMPTY <= ftile_rx_mac_eop_empty;
    RX_MACSI_MAC_FCS_ERROR <= ftile_rx_mac_fcs_error;
    RX_MACSI_MAC_ERROR     <= ftile_rx_mac_error;
    RX_MACSI_MAC_STATUS    <= ftile_rx_mac_status;

    process(ftile_clk_out)
    begin
        if rising_edge(ftile_clk_out) then
            if (MI_RESET_PHY = '1') then
                RX_LINK_UP <= '0';
                TX_LINK_UP <= '0';
            else
                RX_LINK_UP <= ftile_rx_pcs_ready and ftile_rx_pcs_fully_aligned and (not ftile_remote_fault);
                TX_LINK_UP <= ftile_tx_lanes_stable;
            end if;
        end if;
    end process;

    -- Synchronization of REPEATER_CTRL
    sync_repeater_ctrl_i : entity work.ASYNC_BUS_HANDSHAKE
    generic map (
        DATA_WIDTH => ETH_PORT_CHAN
    ) port map (
        ACLK        => MI_CLK_PHY,
        ARST        => MI_RESET_PHY,
        ADATAIN(0)  => mgmt_mac_loop,
        ASEND       => '1',
        AREADY      => open,
        BCLK        => ftile_clk_out,
        BRST        => '0',
        BDATAOUT(0) => sync_repeater_ctrl,
        BLOAD       => '1',
        BVALID      => open
    );

    mac_loopback_i: entity work.macseg_loop
        generic map (
            SEGMENTS => SEGMENTS_LOOP
        )
        port map (
            RST               => RESET_ETH,
            CLK               => ftile_clk_out,

            IN_MAC_DATA       => ftile_rx_mac_data,
            IN_MAC_INFRAME    => ftile_rx_mac_inframe,
            IN_MAC_EOP_EMPTY  => ftile_rx_mac_eop_empty,
            IN_MAC_VALID      => ftile_rx_mac_valid,

            OUT_MAC_DATA      => ftile_tx_loop_data,
            OUT_MAC_INFRAME   => ftile_tx_loop_inframe,
            OUT_MAC_EOP_EMPTY => ftile_tx_loop_eop_empty,
            OUT_MAC_ERROR     => ftile_tx_loop_error,
            OUT_MAC_VALID     => ftile_tx_loop_valid,
            OUT_MAC_READY     => ftile_tx_mac_ready
        );

    ftile_tx_mux: process(all)
    begin
        if sync_repeater_ctrl = '1' then
            -- MAC loopback on
            ftile_tx_mac_data      <= ftile_tx_loop_data;
            ftile_tx_mac_inframe   <= ftile_tx_loop_inframe;
            ftile_tx_mac_eop_empty <= ftile_tx_loop_eop_empty;
            ftile_tx_mac_error     <= ftile_tx_loop_error;
            ftile_tx_mac_valid     <= ftile_tx_loop_valid;
        else
            -- MAC loopback off
            ftile_tx_mac_data      <= TX_MACSI_ADAPT_DATA;
            ftile_tx_mac_inframe   <= TX_MACSI_ADAPT_INFRAME;
            ftile_tx_mac_eop_empty <= TX_MACSI_ADAPT_EOP_EMPTY;
            ftile_tx_mac_error     <= TX_MACSI_ADAPT_ERROR;
            ftile_tx_mac_valid     <= TX_MACSI_ADAPT_VALID;
        end if;
    end process;
end architecture;