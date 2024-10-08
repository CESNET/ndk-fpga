-- usp_phy4x_10g_25g.vhd : Ethernet 10G/25G PHY x4 layer (PCS and PMA sublayers)
--                         core wrapper for Xilinx UltraScale+ FPGA
-- Copyright (C) 2017 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--            Vlastimil Kosar <kosar@brnologic.com>
-- SPDX-License-Identifier: BSD-3-Clause
--
-- NOTE:
--     Address space:
--     0x10000 : ch0 PMA
--     0x30000 : ch0 PCS
--     0x50000 : ch1 PMA
--     0x70000 : ch1 PCS
--     0x90000 : ch2 PMA
--     0xb0000 : ch2 PCS
--     0xd0000 : ch3 PMA
--     0xf0000 : ch3 PCS

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_misc.all;
use work.math_pack.all;
use work.type_pack.all;

entity USP_PCS_PMA_WRAPPER is
generic (
    CH0_MAP           : natural := 0;
    CH1_MAP           : natural := 1;
    CH2_MAP           : natural := 2;
    CH3_MAP           : natural := 3;
    ETH_25G           : boolean := false; -- Enable 25G mode when true
    GTY_TX_EQ         : std_logic_vector(59 downto 0) := X"0000000000C6318";
    MI_DATA_WIDTH_PHY : natural := 32;
    MI_ADDR_WIDTH_PHY : natural := 32
);
port (
    --! \name Clock and reset signals
    RESET          : in  std_logic;
    SYSCLK         : in  std_logic; -- Stable clock, 125 MHz
    --! \name Transceiver reference clock
    REFCLK_P       : in  std_logic;
    REFCLK_N       : in  std_logic;
    --! \name Transceivers 0-3 - serial data
    TX_P           : out std_logic_vector(3 downto 0);
    TX_N           : out std_logic_vector(3 downto 0);
    RX_P           : in  std_logic_vector(3 downto 0);
    RX_N           : in  std_logic_vector(3 downto 0);
    RXPOLARITY     : in  std_logic_vector(4-1 downto 0) := (others => '0');
    TXPOLARITY     : in  std_logic_vector(4-1 downto 0) := (others => '0');
    --! \name XGMII interfaces
    TXRESET        : out std_logic_vector(3 downto 0);
    XGCLK          : out std_logic_vector(3 downto 0);
    TX_LOCAL_FAULT : out std_logic_vector(3 downto 0);
    TXD            : in  std_logic_vector(4*64-1 downto 0);
    TXC            : in  std_logic_vector(4*8-1 downto 0);
    RXRESET        : out std_logic_vector(3 downto 0);
    RXD            : out std_logic_vector(4*64-1 downto 0);
    RXC            : out std_logic_vector(4*8-1 downto 0);
    -- PMD signal detect
    SIGNAL_DETECT  : in  std_logic_vector( 3 downto 0) := (others => '1');
    -- MI32 interface for management
    MI_CLK         : in  std_logic;
    MI_DWR         : in  std_logic_vector(MI_DATA_WIDTH_PHY - 1 downto 0);
    MI_ADDR        : in  std_logic_vector(MI_ADDR_WIDTH_PHY - 1 downto 0);
    MI_RD          : in  std_logic;
    MI_WR          : in  std_logic;
    MI_BE          : in  std_logic_vector(MI_DATA_WIDTH_PHY/8-1 downto 0);
    MI_DRD         : out std_logic_vector(MI_DATA_WIDTH_PHY - 1 downto 0);
    MI_ARDY        : out std_logic;
    MI_DRDY        : out std_logic
);
end entity;


architecture FULL of USP_PCS_PMA_WRAPPER is

type speed_array is array(boolean range <>) of natural;
type cap_array   is array(boolean range <>) of std_logic_vector(15 downto 0);
type nat_array   is array(3 downto 0) of natural;

constant C_SPEED_SEL : speed_array(true downto false) := (25,10);
constant C_CAP_SEL   : cap_array(true downto false) := (X"0800",X"0001");

-- Length of the link status counter. The value of 25 corresponds to 100 ms
constant LINKSTAT_CNTR_LENGTH : integer := 25;
constant CH_MAP : nat_array := (CH3_MAP, CH2_MAP, CH1_MAP, CH0_MAP);

    COMPONENT ten_gig_eth_pcspma
    PORT (
        gt_rxp_in_0 : IN STD_LOGIC;
        gt_rxp_in_1 : IN STD_LOGIC;
        gt_rxp_in_2 : IN STD_LOGIC;
        gt_rxp_in_3 : IN STD_LOGIC;
        gt_rxn_in_0 : IN STD_LOGIC;
        gt_rxn_in_1 : IN STD_LOGIC;
        gt_rxn_in_2 : IN STD_LOGIC;
        gt_rxn_in_3 : IN STD_LOGIC;
        gt_txp_out_0 : OUT STD_LOGIC;
        gt_txp_out_1 : OUT STD_LOGIC;
        gt_txp_out_2 : OUT STD_LOGIC;
        gt_txp_out_3 : OUT STD_LOGIC;
        gt_txn_out_0 : OUT STD_LOGIC;
        gt_txn_out_1 : OUT STD_LOGIC;
        gt_txn_out_2 : OUT STD_LOGIC;
        gt_txn_out_3 : OUT STD_LOGIC;
        rx_core_clk_0 : IN STD_LOGIC;
        rx_core_clk_1 : IN STD_LOGIC;
        rx_core_clk_2 : IN STD_LOGIC;
        rx_core_clk_3 : IN STD_LOGIC;
        txoutclksel_in_0 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        rxoutclksel_in_0 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        txoutclksel_in_1 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        rxoutclksel_in_1 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        txoutclksel_in_2 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        rxoutclksel_in_2 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        txoutclksel_in_3 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        rxoutclksel_in_3 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        gt_dmonitorout_0 : OUT STD_LOGIC_VECTOR(16 DOWNTO 0);
        gt_dmonitorout_1 : OUT STD_LOGIC_VECTOR(16 DOWNTO 0);
        gt_dmonitorout_2 : OUT STD_LOGIC_VECTOR(16 DOWNTO 0);
        gt_dmonitorout_3 : OUT STD_LOGIC_VECTOR(16 DOWNTO 0);
        gt_eyescandataerror_0 : OUT STD_LOGIC;
        gt_eyescandataerror_1 : OUT STD_LOGIC;
        gt_eyescandataerror_2 : OUT STD_LOGIC;
        gt_eyescandataerror_3 : OUT STD_LOGIC;
        gt_eyescanreset_0 : IN STD_LOGIC;
        gt_eyescanreset_1 : IN STD_LOGIC;
        gt_eyescanreset_2 : IN STD_LOGIC;
        gt_eyescanreset_3 : IN STD_LOGIC;
        gt_eyescantrigger_0 : IN STD_LOGIC;
        gt_eyescantrigger_1 : IN STD_LOGIC;
        gt_eyescantrigger_2 : IN STD_LOGIC;
        gt_eyescantrigger_3 : IN STD_LOGIC;
        gt_pcsrsvdin_0 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
        gt_pcsrsvdin_1 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
        gt_pcsrsvdin_2 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
        gt_pcsrsvdin_3 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
        gt_rxbufreset_0 : IN STD_LOGIC;
        gt_rxbufreset_1 : IN STD_LOGIC;
        gt_rxbufreset_2 : IN STD_LOGIC;
        gt_rxbufreset_3 : IN STD_LOGIC;
        gt_rxbufstatus_0 : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
        gt_rxbufstatus_1 : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
        gt_rxbufstatus_2 : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
        gt_rxbufstatus_3 : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
        gt_rxcdrhold_0 : IN STD_LOGIC;
        gt_rxcdrhold_1 : IN STD_LOGIC;
        gt_rxcdrhold_2 : IN STD_LOGIC;
        gt_rxcdrhold_3 : IN STD_LOGIC;
        gt_rxcommadeten_0 : IN STD_LOGIC;
        gt_rxcommadeten_1 : IN STD_LOGIC;
        gt_rxcommadeten_2 : IN STD_LOGIC;
        gt_rxcommadeten_3 : IN STD_LOGIC;
        gt_rxdfeagchold_0 : IN STD_LOGIC;
        gt_rxdfeagchold_1 : IN STD_LOGIC;
        gt_rxdfeagchold_2 : IN STD_LOGIC;
        gt_rxdfeagchold_3 : IN STD_LOGIC;
        gt_rxdfelpmreset_0 : IN STD_LOGIC;
        gt_rxdfelpmreset_1 : IN STD_LOGIC;
        gt_rxdfelpmreset_2 : IN STD_LOGIC;
        gt_rxdfelpmreset_3 : IN STD_LOGIC;
        gt_rxlatclk_0 : IN STD_LOGIC;
        gt_rxlatclk_1 : IN STD_LOGIC;
        gt_rxlatclk_2 : IN STD_LOGIC;
        gt_rxlatclk_3 : IN STD_LOGIC;
        gt_rxlpmen_0 : IN STD_LOGIC;
        gt_rxlpmen_1 : IN STD_LOGIC;
        gt_rxlpmen_2 : IN STD_LOGIC;
        gt_rxlpmen_3 : IN STD_LOGIC;
        gt_rxpcsreset_0 : IN STD_LOGIC;
        gt_rxpcsreset_1 : IN STD_LOGIC;
        gt_rxpcsreset_2 : IN STD_LOGIC;
        gt_rxpcsreset_3 : IN STD_LOGIC;
        gt_rxpmareset_0 : IN STD_LOGIC;
        gt_rxpmareset_1 : IN STD_LOGIC;
        gt_rxpmareset_2 : IN STD_LOGIC;
        gt_rxpmareset_3 : IN STD_LOGIC;
        gt_rxpolarity_0 : IN STD_LOGIC;
        gt_rxpolarity_1 : IN STD_LOGIC;
        gt_rxpolarity_2 : IN STD_LOGIC;
        gt_rxpolarity_3 : IN STD_LOGIC;
        gt_rxprbscntreset_0 : IN STD_LOGIC;
        gt_rxprbscntreset_1 : IN STD_LOGIC;
        gt_rxprbscntreset_2 : IN STD_LOGIC;
        gt_rxprbscntreset_3 : IN STD_LOGIC;
        gt_rxprbserr_0 : OUT STD_LOGIC;
        gt_rxprbserr_1 : OUT STD_LOGIC;
        gt_rxprbserr_2 : OUT STD_LOGIC;
        gt_rxprbserr_3 : OUT STD_LOGIC;
        gt_rxprbssel_0 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        gt_rxprbssel_1 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        gt_rxprbssel_2 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        gt_rxprbssel_3 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        gt_rxrate_0 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        gt_rxrate_1 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        gt_rxrate_2 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        gt_rxrate_3 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        gt_rxslide_in_0 : IN STD_LOGIC;
        gt_rxslide_in_1 : IN STD_LOGIC;
        gt_rxslide_in_2 : IN STD_LOGIC;
        gt_rxslide_in_3 : IN STD_LOGIC;
        gt_rxstartofseq_0 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        gt_rxstartofseq_1 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        gt_rxstartofseq_2 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        gt_rxstartofseq_3 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        gt_txbufstatus_0 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        gt_txbufstatus_1 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        gt_txbufstatus_2 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        gt_txbufstatus_3 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        gt_txdiffctrl_0 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
        gt_txdiffctrl_1 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
        gt_txdiffctrl_2 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
        gt_txdiffctrl_3 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
        gt_txinhibit_0 : IN STD_LOGIC;
        gt_txinhibit_1 : IN STD_LOGIC;
        gt_txinhibit_2 : IN STD_LOGIC;
        gt_txinhibit_3 : IN STD_LOGIC;
        gt_txlatclk_0 : IN STD_LOGIC;
        gt_txlatclk_1 : IN STD_LOGIC;
        gt_txlatclk_2 : IN STD_LOGIC;
        gt_txlatclk_3 : IN STD_LOGIC;
        gt_txmaincursor_0 : IN STD_LOGIC_VECTOR(6 DOWNTO 0);
        gt_txmaincursor_1 : IN STD_LOGIC_VECTOR(6 DOWNTO 0);
        gt_txmaincursor_2 : IN STD_LOGIC_VECTOR(6 DOWNTO 0);
        gt_txmaincursor_3 : IN STD_LOGIC_VECTOR(6 DOWNTO 0);
        gt_txpcsreset_0 : IN STD_LOGIC;
        gt_txpcsreset_1 : IN STD_LOGIC;
        gt_txpcsreset_2 : IN STD_LOGIC;
        gt_txpcsreset_3 : IN STD_LOGIC;
        gt_txpmareset_0 : IN STD_LOGIC;
        gt_txpmareset_1 : IN STD_LOGIC;
        gt_txpmareset_2 : IN STD_LOGIC;
        gt_txpmareset_3 : IN STD_LOGIC;
        gt_txpolarity_0 : IN STD_LOGIC;
        gt_txpolarity_1 : IN STD_LOGIC;
        gt_txpolarity_2 : IN STD_LOGIC;
        gt_txpolarity_3 : IN STD_LOGIC;
        gt_txpostcursor_0 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
        gt_txpostcursor_1 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
        gt_txpostcursor_2 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
        gt_txpostcursor_3 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
        gt_txprbsforceerr_0 : IN STD_LOGIC;
        gt_txprbsforceerr_1 : IN STD_LOGIC;
        gt_txprbsforceerr_2 : IN STD_LOGIC;
        gt_txprbsforceerr_3 : IN STD_LOGIC;
        gt_txprbssel_0 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        gt_txprbssel_1 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        gt_txprbssel_2 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        gt_txprbssel_3 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        gt_txprecursor_0 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
        gt_txprecursor_1 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
        gt_txprecursor_2 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
        gt_txprecursor_3 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
        gtwiz_reset_tx_datapath_0 : IN STD_LOGIC;
        gtwiz_reset_tx_datapath_1 : IN STD_LOGIC;
        gtwiz_reset_tx_datapath_2 : IN STD_LOGIC;
        gtwiz_reset_tx_datapath_3 : IN STD_LOGIC;
        gtwiz_reset_rx_datapath_0 : IN STD_LOGIC;
        gtwiz_reset_rx_datapath_1 : IN STD_LOGIC;
        gtwiz_reset_rx_datapath_2 : IN STD_LOGIC;
        gtwiz_reset_rx_datapath_3 : IN STD_LOGIC;
        rxrecclkout_0 : OUT STD_LOGIC;
        rxrecclkout_1 : OUT STD_LOGIC;
        rxrecclkout_2 : OUT STD_LOGIC;
        rxrecclkout_3 : OUT STD_LOGIC;
        gt_drpclk_0 : IN STD_LOGIC;
        gt_drpclk_1 : IN STD_LOGIC;
        gt_drpclk_2 : IN STD_LOGIC;
        gt_drpclk_3 : IN STD_LOGIC;
        gt_drpdo_0 : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
        gt_drpdo_1 : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
        gt_drpdo_2 : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
        gt_drpdo_3 : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
        gt_drprdy_0 : OUT STD_LOGIC;
        gt_drprdy_1 : OUT STD_LOGIC;
        gt_drprdy_2 : OUT STD_LOGIC;
        gt_drprdy_3 : OUT STD_LOGIC;
        gt_drpen_0 : IN STD_LOGIC;
        gt_drpen_1 : IN STD_LOGIC;
        gt_drpen_2 : IN STD_LOGIC;
        gt_drpen_3 : IN STD_LOGIC;
        gt_drpwe_0 : IN STD_LOGIC;
        gt_drpwe_1 : IN STD_LOGIC;
        gt_drpwe_2 : IN STD_LOGIC;
        gt_drpwe_3 : IN STD_LOGIC;
        gt_drpaddr_0 : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
        gt_drpaddr_1 : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
        gt_drpaddr_2 : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
        gt_drpaddr_3 : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
        gt_drpdi_0 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
        gt_drpdi_1 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
        gt_drpdi_2 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
        gt_drpdi_3 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
        sys_reset : IN STD_LOGIC;
        dclk : IN STD_LOGIC;
        tx_mii_clk_0 : OUT STD_LOGIC;
        tx_mii_clk_1 : OUT STD_LOGIC;
        tx_mii_clk_2 : OUT STD_LOGIC;
        tx_mii_clk_3 : OUT STD_LOGIC;
        rx_clk_out_0 : OUT STD_LOGIC;
        rx_clk_out_1 : OUT STD_LOGIC;
        rx_clk_out_2 : OUT STD_LOGIC;
        rx_clk_out_3 : OUT STD_LOGIC;
        gt_refclk_p : IN STD_LOGIC;
        gt_refclk_n : IN STD_LOGIC;
        gt_refclk_out : OUT STD_LOGIC;
        gtpowergood_out_0 : OUT STD_LOGIC;
        gtpowergood_out_1 : OUT STD_LOGIC;
        gtpowergood_out_2 : OUT STD_LOGIC;
        gtpowergood_out_3 : OUT STD_LOGIC;
        rx_reset_0 : IN STD_LOGIC;
        rx_reset_1 : IN STD_LOGIC;
        rx_reset_2 : IN STD_LOGIC;
        rx_reset_3 : IN STD_LOGIC;
        user_rx_reset_0 : OUT STD_LOGIC;
        user_rx_reset_1 : OUT STD_LOGIC;
        user_rx_reset_2 : OUT STD_LOGIC;
        user_rx_reset_3 : OUT STD_LOGIC;
        rx_mii_d_0 : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
        rx_mii_d_1 : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
        rx_mii_d_2 : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
        rx_mii_d_3 : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
        rx_mii_c_0 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
        rx_mii_c_1 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
        rx_mii_c_2 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
        rx_mii_c_3 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
        ctl_rx_test_pattern_0 : IN STD_LOGIC;
        ctl_rx_test_pattern_1 : IN STD_LOGIC;
        ctl_rx_test_pattern_2 : IN STD_LOGIC;
        ctl_rx_test_pattern_3 : IN STD_LOGIC;
        ctl_rx_data_pattern_select_0 : IN STD_LOGIC;
        ctl_rx_data_pattern_select_1 : IN STD_LOGIC;
        ctl_rx_data_pattern_select_2 : IN STD_LOGIC;
        ctl_rx_data_pattern_select_3 : IN STD_LOGIC;
        ctl_rx_test_pattern_enable_0 : IN STD_LOGIC;
        ctl_rx_test_pattern_enable_1 : IN STD_LOGIC;
        ctl_rx_test_pattern_enable_2 : IN STD_LOGIC;
        ctl_rx_test_pattern_enable_3 : IN STD_LOGIC;
        ctl_rx_prbs31_test_pattern_enable_0 : IN STD_LOGIC;
        ctl_rx_prbs31_test_pattern_enable_1 : IN STD_LOGIC;
        ctl_rx_prbs31_test_pattern_enable_2 : IN STD_LOGIC;
        ctl_rx_prbs31_test_pattern_enable_3 : IN STD_LOGIC;
        stat_rx_framing_err_0 : OUT STD_LOGIC;
        stat_rx_framing_err_1 : OUT STD_LOGIC;
        stat_rx_framing_err_2 : OUT STD_LOGIC;
        stat_rx_framing_err_3 : OUT STD_LOGIC;
        stat_rx_framing_err_valid_0 : OUT STD_LOGIC;
        stat_rx_framing_err_valid_1 : OUT STD_LOGIC;
        stat_rx_framing_err_valid_2 : OUT STD_LOGIC;
        stat_rx_framing_err_valid_3 : OUT STD_LOGIC;
        stat_rx_local_fault_0 : OUT STD_LOGIC;
        stat_rx_local_fault_1 : OUT STD_LOGIC;
        stat_rx_local_fault_2 : OUT STD_LOGIC;
        stat_rx_local_fault_3 : OUT STD_LOGIC;
        stat_rx_block_lock_0 : OUT STD_LOGIC;
        stat_rx_block_lock_1 : OUT STD_LOGIC;
        stat_rx_block_lock_2 : OUT STD_LOGIC;
        stat_rx_block_lock_3 : OUT STD_LOGIC;
        stat_rx_valid_ctrl_code_0 : OUT STD_LOGIC;
        stat_rx_valid_ctrl_code_1 : OUT STD_LOGIC;
        stat_rx_valid_ctrl_code_2 : OUT STD_LOGIC;
        stat_rx_valid_ctrl_code_3 : OUT STD_LOGIC;
        stat_rx_status_0 : OUT STD_LOGIC;
        stat_rx_status_1 : OUT STD_LOGIC;
        stat_rx_status_2 : OUT STD_LOGIC;
        stat_rx_status_3 : OUT STD_LOGIC;
        stat_rx_hi_ber_0 : OUT STD_LOGIC;
        stat_rx_hi_ber_1 : OUT STD_LOGIC;
        stat_rx_hi_ber_2 : OUT STD_LOGIC;
        stat_rx_hi_ber_3 : OUT STD_LOGIC;
        stat_rx_bad_code_0 : OUT STD_LOGIC;
        stat_rx_bad_code_1 : OUT STD_LOGIC;
        stat_rx_bad_code_2 : OUT STD_LOGIC;
        stat_rx_bad_code_3 : OUT STD_LOGIC;
        stat_rx_bad_code_valid_0 : OUT STD_LOGIC;
        stat_rx_bad_code_valid_1 : OUT STD_LOGIC;
        stat_rx_bad_code_valid_2 : OUT STD_LOGIC;
        stat_rx_bad_code_valid_3 : OUT STD_LOGIC;
        stat_rx_error_0 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
        stat_rx_error_1 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
        stat_rx_error_2 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
        stat_rx_error_3 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
        stat_rx_error_valid_0 : OUT STD_LOGIC;
        stat_rx_error_valid_1 : OUT STD_LOGIC;
        stat_rx_error_valid_2 : OUT STD_LOGIC;
        stat_rx_error_valid_3 : OUT STD_LOGIC;
        stat_rx_fifo_error_0 : OUT STD_LOGIC;
        stat_rx_fifo_error_1 : OUT STD_LOGIC;
        stat_rx_fifo_error_2 : OUT STD_LOGIC;
        stat_rx_fifo_error_3 : OUT STD_LOGIC;
        tx_reset_0 : IN STD_LOGIC;
        tx_reset_1 : IN STD_LOGIC;
        tx_reset_2 : IN STD_LOGIC;
        tx_reset_3 : IN STD_LOGIC;
        user_tx_reset_0 : OUT STD_LOGIC;
        user_tx_reset_1 : OUT STD_LOGIC;
        user_tx_reset_2 : OUT STD_LOGIC;
        user_tx_reset_3 : OUT STD_LOGIC;
        tx_mii_d_0 : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
        tx_mii_d_1 : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
        tx_mii_d_2 : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
        tx_mii_d_3 : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
        tx_mii_c_0 : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
        tx_mii_c_1 : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
        tx_mii_c_2 : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
        tx_mii_c_3 : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
        stat_tx_local_fault_0 : OUT STD_LOGIC;
        stat_tx_local_fault_1 : OUT STD_LOGIC;
        stat_tx_local_fault_2 : OUT STD_LOGIC;
        stat_tx_local_fault_3 : OUT STD_LOGIC;
        ctl_tx_test_pattern_0 : IN STD_LOGIC;
        ctl_tx_test_pattern_1 : IN STD_LOGIC;
        ctl_tx_test_pattern_2 : IN STD_LOGIC;
        ctl_tx_test_pattern_3 : IN STD_LOGIC;
        ctl_tx_test_pattern_enable_0 : IN STD_LOGIC;
        ctl_tx_test_pattern_enable_1 : IN STD_LOGIC;
        ctl_tx_test_pattern_enable_2 : IN STD_LOGIC;
        ctl_tx_test_pattern_enable_3 : IN STD_LOGIC;
        ctl_tx_test_pattern_select_0 : IN STD_LOGIC;
        ctl_tx_test_pattern_select_1 : IN STD_LOGIC;
        ctl_tx_test_pattern_select_2 : IN STD_LOGIC;
        ctl_tx_test_pattern_select_3 : IN STD_LOGIC;
        ctl_tx_data_pattern_select_0 : IN STD_LOGIC;
        ctl_tx_data_pattern_select_1 : IN STD_LOGIC;
        ctl_tx_data_pattern_select_2 : IN STD_LOGIC;
        ctl_tx_data_pattern_select_3 : IN STD_LOGIC;
        ctl_tx_test_pattern_seed_a_0 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
        ctl_tx_test_pattern_seed_a_1 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
        ctl_tx_test_pattern_seed_a_2 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
        ctl_tx_test_pattern_seed_a_3 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
        ctl_tx_test_pattern_seed_b_0 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
        ctl_tx_test_pattern_seed_b_1 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
        ctl_tx_test_pattern_seed_b_2 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
        ctl_tx_test_pattern_seed_b_3 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
        ctl_tx_prbs31_test_pattern_enable_0 : IN STD_LOGIC;
        ctl_tx_prbs31_test_pattern_enable_1 : IN STD_LOGIC;
        ctl_tx_prbs31_test_pattern_enable_2 : IN STD_LOGIC;
        ctl_tx_prbs31_test_pattern_enable_3 : IN STD_LOGIC;
        gt_loopback_in_0 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        gt_loopback_in_1 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        gt_loopback_in_2 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        gt_loopback_in_3 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        gt_rxprbslocked_0 : OUT STD_LOGIC_VECTOR ( 0 to 0 );
        gt_rxprbslocked_1 : OUT STD_LOGIC_VECTOR ( 0 to 0 );
        gt_rxprbslocked_2 : OUT STD_LOGIC_VECTOR ( 0 to 0 );
        gt_rxprbslocked_3 : OUT STD_LOGIC_VECTOR ( 0 to 0 );
        gt_txresetdone_0  : OUT STD_LOGIC_VECTOR ( 0 to 0 );
        gt_txresetdone_1  : OUT STD_LOGIC_VECTOR ( 0 to 0 );
        gt_txresetdone_2  : OUT STD_LOGIC_VECTOR ( 0 to 0 );
        gt_txresetdone_3  : OUT STD_LOGIC_VECTOR ( 0 to 0 );
        gt_txelecidle_0   :  IN STD_LOGIC_VECTOR ( 0 to 0 );
        gt_txelecidle_1   :  IN STD_LOGIC_VECTOR ( 0 to 0 );
        gt_txelecidle_2   :  IN STD_LOGIC_VECTOR ( 0 to 0 );
        gt_txelecidle_3   :  IN STD_LOGIC_VECTOR ( 0 to 0 );
        gt_drprst_0       :  IN STD_LOGIC;
        gt_drprst_1       :  IN STD_LOGIC;
        gt_drprst_2       :  IN STD_LOGIC;
        gt_drprst_3       :  IN STD_LOGIC;
        qpllreset_in_0    :  IN STD_LOGIC
    );
    END COMPONENT;

    COMPONENT twenty_five_gig_eth_pcspma
        PORT (
            gt_rxp_in_0 : IN STD_LOGIC;
            gt_rxp_in_1 : IN STD_LOGIC;
            gt_rxp_in_2 : IN STD_LOGIC;
            gt_rxp_in_3 : IN STD_LOGIC;
            gt_rxn_in_0 : IN STD_LOGIC;
            gt_rxn_in_1 : IN STD_LOGIC;
            gt_rxn_in_2 : IN STD_LOGIC;
            gt_rxn_in_3 : IN STD_LOGIC;
            gt_txp_out_0 : OUT STD_LOGIC;
            gt_txp_out_1 : OUT STD_LOGIC;
            gt_txp_out_2 : OUT STD_LOGIC;
            gt_txp_out_3 : OUT STD_LOGIC;
            gt_txn_out_0 : OUT STD_LOGIC;
            gt_txn_out_1 : OUT STD_LOGIC;
            gt_txn_out_2 : OUT STD_LOGIC;
            gt_txn_out_3 : OUT STD_LOGIC;
            rx_core_clk_0 : IN STD_LOGIC;
            rx_core_clk_1 : IN STD_LOGIC;
            rx_core_clk_2 : IN STD_LOGIC;
            rx_core_clk_3 : IN STD_LOGIC;
            txoutclksel_in_0 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            rxoutclksel_in_0 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            txoutclksel_in_1 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            rxoutclksel_in_1 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            txoutclksel_in_2 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            rxoutclksel_in_2 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            txoutclksel_in_3 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            rxoutclksel_in_3 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            gt_dmonitorout_0 : OUT STD_LOGIC_VECTOR(16 DOWNTO 0);
            gt_dmonitorout_1 : OUT STD_LOGIC_VECTOR(16 DOWNTO 0);
            gt_dmonitorout_2 : OUT STD_LOGIC_VECTOR(16 DOWNTO 0);
            gt_dmonitorout_3 : OUT STD_LOGIC_VECTOR(16 DOWNTO 0);
            gt_eyescandataerror_0 : OUT STD_LOGIC;
            gt_eyescandataerror_1 : OUT STD_LOGIC;
            gt_eyescandataerror_2 : OUT STD_LOGIC;
            gt_eyescandataerror_3 : OUT STD_LOGIC;
            gt_eyescanreset_0 : IN STD_LOGIC;
            gt_eyescanreset_1 : IN STD_LOGIC;
            gt_eyescanreset_2 : IN STD_LOGIC;
            gt_eyescanreset_3 : IN STD_LOGIC;
            gt_eyescantrigger_0 : IN STD_LOGIC;
            gt_eyescantrigger_1 : IN STD_LOGIC;
            gt_eyescantrigger_2 : IN STD_LOGIC;
            gt_eyescantrigger_3 : IN STD_LOGIC;
            gt_pcsrsvdin_0 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
            gt_pcsrsvdin_1 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
            gt_pcsrsvdin_2 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
            gt_pcsrsvdin_3 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
            gt_rxbufreset_0 : IN STD_LOGIC;
            gt_rxbufreset_1 : IN STD_LOGIC;
            gt_rxbufreset_2 : IN STD_LOGIC;
            gt_rxbufreset_3 : IN STD_LOGIC;
            gt_rxbufstatus_0 : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
            gt_rxbufstatus_1 : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
            gt_rxbufstatus_2 : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
            gt_rxbufstatus_3 : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
            gt_rxcdrhold_0 : IN STD_LOGIC;
            gt_rxcdrhold_1 : IN STD_LOGIC;
            gt_rxcdrhold_2 : IN STD_LOGIC;
            gt_rxcdrhold_3 : IN STD_LOGIC;
            gt_rxcommadeten_0 : IN STD_LOGIC;
            gt_rxcommadeten_1 : IN STD_LOGIC;
            gt_rxcommadeten_2 : IN STD_LOGIC;
            gt_rxcommadeten_3 : IN STD_LOGIC;
            gt_rxdfeagchold_0 : IN STD_LOGIC;
            gt_rxdfeagchold_1 : IN STD_LOGIC;
            gt_rxdfeagchold_2 : IN STD_LOGIC;
            gt_rxdfeagchold_3 : IN STD_LOGIC;
            gt_rxdfelpmreset_0 : IN STD_LOGIC;
            gt_rxdfelpmreset_1 : IN STD_LOGIC;
            gt_rxdfelpmreset_2 : IN STD_LOGIC;
            gt_rxdfelpmreset_3 : IN STD_LOGIC;
            gt_rxlatclk_0 : IN STD_LOGIC;
            gt_rxlatclk_1 : IN STD_LOGIC;
            gt_rxlatclk_2 : IN STD_LOGIC;
            gt_rxlatclk_3 : IN STD_LOGIC;
            gt_rxlpmen_0 : IN STD_LOGIC;
            gt_rxlpmen_1 : IN STD_LOGIC;
            gt_rxlpmen_2 : IN STD_LOGIC;
            gt_rxlpmen_3 : IN STD_LOGIC;
            gt_rxpcsreset_0 : IN STD_LOGIC;
            gt_rxpcsreset_1 : IN STD_LOGIC;
            gt_rxpcsreset_2 : IN STD_LOGIC;
            gt_rxpcsreset_3 : IN STD_LOGIC;
            gt_rxpmareset_0 : IN STD_LOGIC;
            gt_rxpmareset_1 : IN STD_LOGIC;
            gt_rxpmareset_2 : IN STD_LOGIC;
            gt_rxpmareset_3 : IN STD_LOGIC;
            gt_rxpolarity_0 : IN STD_LOGIC;
            gt_rxpolarity_1 : IN STD_LOGIC;
            gt_rxpolarity_2 : IN STD_LOGIC;
            gt_rxpolarity_3 : IN STD_LOGIC;
            gt_rxprbscntreset_0 : IN STD_LOGIC;
            gt_rxprbscntreset_1 : IN STD_LOGIC;
            gt_rxprbscntreset_2 : IN STD_LOGIC;
            gt_rxprbscntreset_3 : IN STD_LOGIC;
            gt_rxprbserr_0 : OUT STD_LOGIC;
            gt_rxprbserr_1 : OUT STD_LOGIC;
            gt_rxprbserr_2 : OUT STD_LOGIC;
            gt_rxprbserr_3 : OUT STD_LOGIC;
            gt_rxprbssel_0 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
            gt_rxprbssel_1 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
            gt_rxprbssel_2 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
            gt_rxprbssel_3 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
            gt_rxrate_0 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            gt_rxrate_1 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            gt_rxrate_2 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            gt_rxrate_3 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            gt_rxslide_in_0 : IN STD_LOGIC;
            gt_rxslide_in_1 : IN STD_LOGIC;
            gt_rxslide_in_2 : IN STD_LOGIC;
            gt_rxslide_in_3 : IN STD_LOGIC;
            gt_rxstartofseq_0 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
            gt_rxstartofseq_1 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
            gt_rxstartofseq_2 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
            gt_rxstartofseq_3 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
            gt_txbufstatus_0 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
            gt_txbufstatus_1 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
            gt_txbufstatus_2 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
            gt_txbufstatus_3 : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
            gt_txdiffctrl_0 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
            gt_txdiffctrl_1 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
            gt_txdiffctrl_2 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
            gt_txdiffctrl_3 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
            gt_txinhibit_0 : IN STD_LOGIC;
            gt_txinhibit_1 : IN STD_LOGIC;
            gt_txinhibit_2 : IN STD_LOGIC;
            gt_txinhibit_3 : IN STD_LOGIC;
            gt_txlatclk_0 : IN STD_LOGIC;
            gt_txlatclk_1 : IN STD_LOGIC;
            gt_txlatclk_2 : IN STD_LOGIC;
            gt_txlatclk_3 : IN STD_LOGIC;
            gt_txmaincursor_0 : IN STD_LOGIC_VECTOR(6 DOWNTO 0);
            gt_txmaincursor_1 : IN STD_LOGIC_VECTOR(6 DOWNTO 0);
            gt_txmaincursor_2 : IN STD_LOGIC_VECTOR(6 DOWNTO 0);
            gt_txmaincursor_3 : IN STD_LOGIC_VECTOR(6 DOWNTO 0);
            gt_txpcsreset_0 : IN STD_LOGIC;
            gt_txpcsreset_1 : IN STD_LOGIC;
            gt_txpcsreset_2 : IN STD_LOGIC;
            gt_txpcsreset_3 : IN STD_LOGIC;
            gt_txpmareset_0 : IN STD_LOGIC;
            gt_txpmareset_1 : IN STD_LOGIC;
            gt_txpmareset_2 : IN STD_LOGIC;
            gt_txpmareset_3 : IN STD_LOGIC;
            gt_txpolarity_0 : IN STD_LOGIC;
            gt_txpolarity_1 : IN STD_LOGIC;
            gt_txpolarity_2 : IN STD_LOGIC;
            gt_txpolarity_3 : IN STD_LOGIC;
            gt_txpostcursor_0 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
            gt_txpostcursor_1 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
            gt_txpostcursor_2 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
            gt_txpostcursor_3 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
            gt_txprbsforceerr_0 : IN STD_LOGIC;
            gt_txprbsforceerr_1 : IN STD_LOGIC;
            gt_txprbsforceerr_2 : IN STD_LOGIC;
            gt_txprbsforceerr_3 : IN STD_LOGIC;
            gt_txprbssel_0 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
            gt_txprbssel_1 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
            gt_txprbssel_2 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
            gt_txprbssel_3 : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
            gt_txprecursor_0 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
            gt_txprecursor_1 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
            gt_txprecursor_2 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
            gt_txprecursor_3 : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
            gtwiz_reset_tx_datapath_0 : IN STD_LOGIC;
            gtwiz_reset_tx_datapath_1 : IN STD_LOGIC;
            gtwiz_reset_tx_datapath_2 : IN STD_LOGIC;
            gtwiz_reset_tx_datapath_3 : IN STD_LOGIC;
            gtwiz_reset_rx_datapath_0 : IN STD_LOGIC;
            gtwiz_reset_rx_datapath_1 : IN STD_LOGIC;
            gtwiz_reset_rx_datapath_2 : IN STD_LOGIC;
            gtwiz_reset_rx_datapath_3 : IN STD_LOGIC;
            rxrecclkout_0 : OUT STD_LOGIC;
            rxrecclkout_1 : OUT STD_LOGIC;
            rxrecclkout_2 : OUT STD_LOGIC;
            rxrecclkout_3 : OUT STD_LOGIC;
            gt_drpclk_0 : IN STD_LOGIC;
            gt_drpclk_1 : IN STD_LOGIC;
            gt_drpclk_2 : IN STD_LOGIC;
            gt_drpclk_3 : IN STD_LOGIC;
            gt_drpdo_0 : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
            gt_drpdo_1 : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
            gt_drpdo_2 : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
            gt_drpdo_3 : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
            gt_drprdy_0 : OUT STD_LOGIC;
            gt_drprdy_1 : OUT STD_LOGIC;
            gt_drprdy_2 : OUT STD_LOGIC;
            gt_drprdy_3 : OUT STD_LOGIC;
            gt_drpen_0 : IN STD_LOGIC;
            gt_drpen_1 : IN STD_LOGIC;
            gt_drpen_2 : IN STD_LOGIC;
            gt_drpen_3 : IN STD_LOGIC;
            gt_drpwe_0 : IN STD_LOGIC;
            gt_drpwe_1 : IN STD_LOGIC;
            gt_drpwe_2 : IN STD_LOGIC;
            gt_drpwe_3 : IN STD_LOGIC;
            gt_drpaddr_0 : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
            gt_drpaddr_1 : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
            gt_drpaddr_2 : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
            gt_drpaddr_3 : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
            gt_drpdi_0 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
            gt_drpdi_1 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
            gt_drpdi_2 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
            gt_drpdi_3 : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
            sys_reset : IN STD_LOGIC;
            dclk : IN STD_LOGIC;
            tx_mii_clk_0 : OUT STD_LOGIC;
            tx_mii_clk_1 : OUT STD_LOGIC;
            tx_mii_clk_2 : OUT STD_LOGIC;
            tx_mii_clk_3 : OUT STD_LOGIC;
            rx_clk_out_0 : OUT STD_LOGIC;
            rx_clk_out_1 : OUT STD_LOGIC;
            rx_clk_out_2 : OUT STD_LOGIC;
            rx_clk_out_3 : OUT STD_LOGIC;
            gt_refclk_p : IN STD_LOGIC;
            gt_refclk_n : IN STD_LOGIC;
            gt_refclk_out : OUT STD_LOGIC;
            gtpowergood_out_0 : OUT STD_LOGIC;
            gtpowergood_out_1 : OUT STD_LOGIC;
            gtpowergood_out_2 : OUT STD_LOGIC;
            gtpowergood_out_3 : OUT STD_LOGIC;
            rx_reset_0 : IN STD_LOGIC;
            rx_reset_1 : IN STD_LOGIC;
            rx_reset_2 : IN STD_LOGIC;
            rx_reset_3 : IN STD_LOGIC;
            user_rx_reset_0 : OUT STD_LOGIC;
            user_rx_reset_1 : OUT STD_LOGIC;
            user_rx_reset_2 : OUT STD_LOGIC;
            user_rx_reset_3 : OUT STD_LOGIC;
            rx_mii_d_0 : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
            rx_mii_d_1 : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
            rx_mii_d_2 : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
            rx_mii_d_3 : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
            rx_mii_c_0 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
            rx_mii_c_1 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
            rx_mii_c_2 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
            rx_mii_c_3 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
            ctl_rx_test_pattern_0 : IN STD_LOGIC;
            ctl_rx_test_pattern_1 : IN STD_LOGIC;
            ctl_rx_test_pattern_2 : IN STD_LOGIC;
            ctl_rx_test_pattern_3 : IN STD_LOGIC;
            ctl_rx_data_pattern_select_0 : IN STD_LOGIC;
            ctl_rx_data_pattern_select_1 : IN STD_LOGIC;
            ctl_rx_data_pattern_select_2 : IN STD_LOGIC;
            ctl_rx_data_pattern_select_3 : IN STD_LOGIC;
            ctl_rx_test_pattern_enable_0 : IN STD_LOGIC;
            ctl_rx_test_pattern_enable_1 : IN STD_LOGIC;
            ctl_rx_test_pattern_enable_2 : IN STD_LOGIC;
            ctl_rx_test_pattern_enable_3 : IN STD_LOGIC;
            ctl_rx_prbs31_test_pattern_enable_0 : IN STD_LOGIC;
            ctl_rx_prbs31_test_pattern_enable_1 : IN STD_LOGIC;
            ctl_rx_prbs31_test_pattern_enable_2 : IN STD_LOGIC;
            ctl_rx_prbs31_test_pattern_enable_3 : IN STD_LOGIC;
            stat_rx_framing_err_0 : OUT STD_LOGIC;
            stat_rx_framing_err_1 : OUT STD_LOGIC;
            stat_rx_framing_err_2 : OUT STD_LOGIC;
            stat_rx_framing_err_3 : OUT STD_LOGIC;
            stat_rx_framing_err_valid_0 : OUT STD_LOGIC;
            stat_rx_framing_err_valid_1 : OUT STD_LOGIC;
            stat_rx_framing_err_valid_2 : OUT STD_LOGIC;
            stat_rx_framing_err_valid_3 : OUT STD_LOGIC;
            stat_rx_local_fault_0 : OUT STD_LOGIC;
            stat_rx_local_fault_1 : OUT STD_LOGIC;
            stat_rx_local_fault_2 : OUT STD_LOGIC;
            stat_rx_local_fault_3 : OUT STD_LOGIC;
            stat_rx_block_lock_0 : OUT STD_LOGIC;
            stat_rx_block_lock_1 : OUT STD_LOGIC;
            stat_rx_block_lock_2 : OUT STD_LOGIC;
            stat_rx_block_lock_3 : OUT STD_LOGIC;
            stat_rx_valid_ctrl_code_0 : OUT STD_LOGIC;
            stat_rx_valid_ctrl_code_1 : OUT STD_LOGIC;
            stat_rx_valid_ctrl_code_2 : OUT STD_LOGIC;
            stat_rx_valid_ctrl_code_3 : OUT STD_LOGIC;
            stat_rx_status_0 : OUT STD_LOGIC;
            stat_rx_status_1 : OUT STD_LOGIC;
            stat_rx_status_2 : OUT STD_LOGIC;
            stat_rx_status_3 : OUT STD_LOGIC;
            stat_rx_hi_ber_0 : OUT STD_LOGIC;
            stat_rx_hi_ber_1 : OUT STD_LOGIC;
            stat_rx_hi_ber_2 : OUT STD_LOGIC;
            stat_rx_hi_ber_3 : OUT STD_LOGIC;
            stat_rx_bad_code_0 : OUT STD_LOGIC;
            stat_rx_bad_code_1 : OUT STD_LOGIC;
            stat_rx_bad_code_2 : OUT STD_LOGIC;
            stat_rx_bad_code_3 : OUT STD_LOGIC;
            stat_rx_bad_code_valid_0 : OUT STD_LOGIC;
            stat_rx_bad_code_valid_1 : OUT STD_LOGIC;
            stat_rx_bad_code_valid_2 : OUT STD_LOGIC;
            stat_rx_bad_code_valid_3 : OUT STD_LOGIC;
            stat_rx_error_0 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
            stat_rx_error_1 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
            stat_rx_error_2 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
            stat_rx_error_3 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
            stat_rx_error_valid_0 : OUT STD_LOGIC;
            stat_rx_error_valid_1 : OUT STD_LOGIC;
            stat_rx_error_valid_2 : OUT STD_LOGIC;
            stat_rx_error_valid_3 : OUT STD_LOGIC;
            stat_rx_fifo_error_0 : OUT STD_LOGIC;
            stat_rx_fifo_error_1 : OUT STD_LOGIC;
            stat_rx_fifo_error_2 : OUT STD_LOGIC;
            stat_rx_fifo_error_3 : OUT STD_LOGIC;
            tx_reset_0 : IN STD_LOGIC;
            tx_reset_1 : IN STD_LOGIC;
            tx_reset_2 : IN STD_LOGIC;
            tx_reset_3 : IN STD_LOGIC;
            user_tx_reset_0 : OUT STD_LOGIC;
            user_tx_reset_1 : OUT STD_LOGIC;
            user_tx_reset_2 : OUT STD_LOGIC;
            user_tx_reset_3 : OUT STD_LOGIC;
            tx_mii_d_0 : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
            tx_mii_d_1 : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
            tx_mii_d_2 : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
            tx_mii_d_3 : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
            tx_mii_c_0 : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
            tx_mii_c_1 : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
            tx_mii_c_2 : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
            tx_mii_c_3 : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
            stat_tx_local_fault_0 : OUT STD_LOGIC;
            stat_tx_local_fault_1 : OUT STD_LOGIC;
            stat_tx_local_fault_2 : OUT STD_LOGIC;
            stat_tx_local_fault_3 : OUT STD_LOGIC;
            ctl_tx_test_pattern_0 : IN STD_LOGIC;
            ctl_tx_test_pattern_1 : IN STD_LOGIC;
            ctl_tx_test_pattern_2 : IN STD_LOGIC;
            ctl_tx_test_pattern_3 : IN STD_LOGIC;
            ctl_tx_test_pattern_enable_0 : IN STD_LOGIC;
            ctl_tx_test_pattern_enable_1 : IN STD_LOGIC;
            ctl_tx_test_pattern_enable_2 : IN STD_LOGIC;
            ctl_tx_test_pattern_enable_3 : IN STD_LOGIC;
            ctl_tx_test_pattern_select_0 : IN STD_LOGIC;
            ctl_tx_test_pattern_select_1 : IN STD_LOGIC;
            ctl_tx_test_pattern_select_2 : IN STD_LOGIC;
            ctl_tx_test_pattern_select_3 : IN STD_LOGIC;
            ctl_tx_data_pattern_select_0 : IN STD_LOGIC;
            ctl_tx_data_pattern_select_1 : IN STD_LOGIC;
            ctl_tx_data_pattern_select_2 : IN STD_LOGIC;
            ctl_tx_data_pattern_select_3 : IN STD_LOGIC;
            ctl_tx_test_pattern_seed_a_0 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
            ctl_tx_test_pattern_seed_a_1 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
            ctl_tx_test_pattern_seed_a_2 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
            ctl_tx_test_pattern_seed_a_3 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
            ctl_tx_test_pattern_seed_b_0 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
            ctl_tx_test_pattern_seed_b_1 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
            ctl_tx_test_pattern_seed_b_2 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
            ctl_tx_test_pattern_seed_b_3 : IN STD_LOGIC_VECTOR(57 DOWNTO 0);
            ctl_tx_prbs31_test_pattern_enable_0 : IN STD_LOGIC;
            ctl_tx_prbs31_test_pattern_enable_1 : IN STD_LOGIC;
            ctl_tx_prbs31_test_pattern_enable_2 : IN STD_LOGIC;
            ctl_tx_prbs31_test_pattern_enable_3 : IN STD_LOGIC;
            gt_loopback_in_0 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            gt_loopback_in_1 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            gt_loopback_in_2 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            gt_loopback_in_3 : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
            gt_rxprbslocked_0 : OUT STD_LOGIC_VECTOR ( 0 to 0 );
            gt_rxprbslocked_1 : OUT STD_LOGIC_VECTOR ( 0 to 0 );
            gt_rxprbslocked_2 : OUT STD_LOGIC_VECTOR ( 0 to 0 );
            gt_rxprbslocked_3 : OUT STD_LOGIC_VECTOR ( 0 to 0 );
            gt_txresetdone_0  : OUT STD_LOGIC_VECTOR ( 0 to 0 );
            gt_txresetdone_1  : OUT STD_LOGIC_VECTOR ( 0 to 0 );
            gt_txresetdone_2  : OUT STD_LOGIC_VECTOR ( 0 to 0 );
            gt_txresetdone_3  : OUT STD_LOGIC_VECTOR ( 0 to 0 );
            gt_txelecidle_0   :  IN STD_LOGIC_VECTOR ( 0 to 0 );
            gt_txelecidle_1   :  IN STD_LOGIC_VECTOR ( 0 to 0 );
            gt_txelecidle_2   :  IN STD_LOGIC_VECTOR ( 0 to 0 );
            gt_txelecidle_3   :  IN STD_LOGIC_VECTOR ( 0 to 0 );
            gt_drprst_0       :  IN STD_LOGIC;
            gt_drprst_1       :  IN STD_LOGIC;
            gt_drprst_2       :  IN STD_LOGIC;
            gt_drprst_3       :  IN STD_LOGIC;
            qpllreset_in_0    :  IN STD_LOGIC
        );
    END COMPONENT;

    constant MI_ADDR_BASES_PHY   : natural := 4;
    constant MGMT_OFF            : std_logic_vector(MI_ADDR_WIDTH_PHY-1 downto 0) := X"0004_0000";

    function mi_addr_base_init_phy_f return slv_array_t is
        variable mi_addr_base_var : slv_array_t(MI_ADDR_BASES_PHY-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    begin
        for i in 0 to MI_ADDR_BASES_PHY-1 loop
            mi_addr_base_var(i) := std_logic_vector(resize(i*unsigned(MGMT_OFF), MI_ADDR_WIDTH_PHY));
        end loop;
        return mi_addr_base_var;
    end function;

    signal mi_split_dwr          : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal mi_split_addr         : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    signal mi_split_rd           : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);
    signal mi_split_wr           : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);
    signal mi_split_be           : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_DATA_WIDTH_PHY/8-1 downto 0);
    signal mi_split_ardy         : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);
    signal mi_split_drd          : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal mi_split_drdy         : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);

    signal eth0_clk                   : std_logic_vector(3 downto 0);
    signal eth0_txreset               : std_logic_vector(3 downto 0);
    signal eth0_rxreset               : std_logic_vector(3 downto 0);
    signal eth0_txreset_a             : std_logic_vector(3 downto 0);
    signal eth0_rxreset_a             : std_logic_vector(3 downto 0);
    signal eth0_pma_txreset           : std_logic_vector(3 downto 0);
    signal eth0_pma_rxreset           : std_logic_vector(3 downto 0);
    signal eth0_core_clk              : std_logic_vector(3 downto 0);
    signal eth0_rx_usr_rst            : std_logic_vector(3 downto 0);
    signal eth0_rxd                   : std_logic_vector(4*64-1 downto 0);
    signal eth0_rxc                   : std_logic_vector(4*8-1 downto 0);
    signal ber_cntr_clk               : std_logic_vector(3 downto 0);
    signal blk_cntr_clk               : std_logic_vector(3 downto 0);
    signal ber_mon_reset              : std_logic_vector(3 downto 0);

    signal hi_ber                     : std_logic_vector(3 downto 0);
    signal blk_lock                   : std_logic_vector(3 downto 0);
    signal link_status                : std_logic_vector(3 downto 0);
    signal link_status_sync           : std_logic_vector(3 downto 0);
    signal framing_err                : std_logic_vector(3 downto 0);
    signal framing_err_vld            : std_logic_vector(3 downto 0);
    signal ber_mon_sh                 : std_logic_vector(4*2-1 downto 0);
    signal ber_cnt_clr                : std_logic_vector(3 downto 0);
    signal ber_cnt_clr_sync           : std_logic_vector(3 downto 0);
    signal ber_count                  : std_logic_vector(4*22-1 downto 0);
    signal blk_err_clr                : std_logic_vector(3 downto 0);
    signal blk_err_clr_sync           : std_logic_vector(3 downto 0);
    signal blk_err_cntr               : std_logic_vector(4*22-1 downto 0);
    signal bad_code                   : std_logic_vector(3 downto 0);
    signal bad_code_vld               : std_logic_vector(3 downto 0);
    signal pma_reset                  : std_logic_vector(3 downto 0);
    signal pcs_reset                  : std_logic_vector(3 downto 0);
    signal pma_lpbck                  : std_logic_vector(3 downto 0);
    signal pma_rem_lpbck              : std_logic_vector(3 downto 0);
    signal gt_loopback                : std_logic_vector(4*3-1 downto 0);
    signal gt_rxpolarity_async        : std_logic_vector(RXPOLARITY'range);
    signal gt_txpolarity_async        : std_logic_vector(TXPOLARITY'range);
    signal gt_rxpolarity              : std_logic_vector(RXPOLARITY'range);
    signal gt_txpolarity              : std_logic_vector(TXPOLARITY'range);

    signal link_cntr                  : std_logic_vector(LINKSTAT_CNTR_LENGTH*4-1 downto 0);
    signal rx_link_rst                : std_logic_vector(3 downto 0);
    signal gt_precursor               : std_logic_vector(31 downto 0);
    signal gt_postcursor              : std_logic_vector(31 downto 0);
    signal gt_txdiffctrl              : std_logic_vector(31 downto 0);

    --
    signal drpaddr                   : std_logic_vector(4*16-1 downto 0);
    signal drpdi                     : std_logic_vector(4*16-1 downto 0);
    signal drpwe                     : std_logic_vector(4-1 downto 0);
    signal drpsel                    : std_logic_vector( 3 downto 0);
    signal drpdo                     : std_logic_vector(4*16-1 downto 0);
    signal drprdy                    : std_logic_vector(4-1 downto 0);
    signal drpen                     : std_logic_vector(4-1 downto 0);


begin


---------------------------------------------------------------------------
--  10 Gig Ethe PCS/PMA core
---------------------------------------------------------------------------

GEN_10GE: if (not ETH_25G) generate

    ETH10G_I : ten_gig_eth_pcspma
    PORT MAP (
        sys_reset     => RESET,
        dclk          => SYSCLK,
        --
        gt_rxp_in_0   => RX_P(0),
        gt_rxp_in_1   => RX_P(1),
        gt_rxp_in_2   => RX_P(2),
        gt_rxp_in_3   => RX_P(3),
        --
        gt_rxn_in_0   => RX_N(0),
        gt_rxn_in_1   => RX_N(1),
        gt_rxn_in_2   => RX_N(2),
        gt_rxn_in_3   => RX_N(3),
        --
        gt_txp_out_0  => TX_P(0),
        gt_txp_out_1  => TX_P(1),
        gt_txp_out_2  => TX_P(2),
        gt_txp_out_3  => TX_P(3),
        --
        gt_txn_out_0  => TX_N(0),
        gt_txn_out_1  => TX_N(1),
        gt_txn_out_2  => TX_N(2),
        gt_txn_out_3  => TX_N(3),
        --
        rx_core_clk_0 => eth0_clk(CH0_MAP), -- eth0_core_clk(0), -- IN
        rx_core_clk_1 => eth0_clk(CH1_MAP), -- eth0_core_clk(1),
        rx_core_clk_2 => eth0_clk(CH2_MAP), -- eth0_core_clk(2),
        rx_core_clk_3 => eth0_clk(CH3_MAP), -- eth0_core_clk(3),
        --
        gtwiz_reset_tx_datapath_0 => eth0_pma_txreset(CH0_MAP),
        gtwiz_reset_tx_datapath_1 => eth0_pma_txreset(CH1_MAP),
        gtwiz_reset_tx_datapath_2 => eth0_pma_txreset(CH2_MAP),
        gtwiz_reset_tx_datapath_3 => eth0_pma_txreset(CH3_MAP),
        --
        gtwiz_reset_rx_datapath_0 => eth0_pma_rxreset(CH0_MAP),
        gtwiz_reset_rx_datapath_1 => eth0_pma_rxreset(CH1_MAP),
        gtwiz_reset_rx_datapath_2 => eth0_pma_rxreset(CH2_MAP),
        gtwiz_reset_rx_datapath_3 => eth0_pma_rxreset(CH3_MAP),
        rxrecclkout_0 => open,
        rxrecclkout_1 => open,
        rxrecclkout_2 => open,
        rxrecclkout_3 => open,
        tx_mii_clk_0 => eth0_clk(CH0_MAP), -- out -> txusrclk2
        tx_mii_clk_1 => eth0_clk(CH1_MAP),
        tx_mii_clk_2 => eth0_clk(CH2_MAP),
        tx_mii_clk_3 => eth0_clk(CH3_MAP),
        rx_clk_out_0 => eth0_core_clk(CH0_MAP), -- out -> rxusrclk2
        rx_clk_out_1 => eth0_core_clk(CH1_MAP),
        rx_clk_out_2 => eth0_core_clk(CH2_MAP),
        rx_clk_out_3 => eth0_core_clk(CH3_MAP),
        gt_refclk_p => REFCLK_P,
        gt_refclk_n => REFCLK_N,
        gt_refclk_out => open,

        gtpowergood_out_0 => open,
        gtpowergood_out_1 => open,
        gtpowergood_out_2 => open,
        gtpowergood_out_3 => open,
        rx_reset_0 => eth0_rxreset(CH0_MAP),
        rx_reset_1 => eth0_rxreset(CH1_MAP),
        rx_reset_2 => eth0_rxreset(CH2_MAP),
        rx_reset_3 => eth0_rxreset(CH3_MAP),
        user_rx_reset_0 => eth0_rx_usr_rst(CH0_MAP), -- RXRESET(CH0_MAP),
        user_rx_reset_1 => eth0_rx_usr_rst(CH1_MAP), -- RXRESET(CH1_MAP),
        user_rx_reset_2 => eth0_rx_usr_rst(CH2_MAP), -- RXRESET(CH2_MAP),
        user_rx_reset_3 => eth0_rx_usr_rst(CH3_MAP), -- RXRESET(CH3_MAP),
        --
        txoutclksel_in_0 => "101",
        txoutclksel_in_1 => "101",
        txoutclksel_in_2 => "101",
        txoutclksel_in_3 => "101",
        rxoutclksel_in_0 => "101",
        rxoutclksel_in_1 => "101",
        rxoutclksel_in_2 => "101",
        rxoutclksel_in_3 => "101",
        --
        gt_eyescanreset_0 => '0',
        gt_eyescanreset_1 => '0',
        gt_eyescanreset_2 => '0',
        gt_eyescanreset_3 => '0',
        gt_eyescantrigger_0 => '0',
        gt_eyescantrigger_1 => '0',
        gt_eyescantrigger_2 => '0',
        gt_eyescantrigger_3 => '0',
        gt_pcsrsvdin_0 => (others => '0'),
        gt_pcsrsvdin_1 => (others => '0'),
        gt_pcsrsvdin_2 => (others => '0'),
        gt_pcsrsvdin_3 => (others => '0'),
        gt_rxbufreset_0 => '0',
        gt_rxbufreset_1 => '0',
        gt_rxbufreset_2 => '0',
        gt_rxbufreset_3 => '0',
        gt_rxcdrhold_0    => '0',
        gt_rxcdrhold_1    => '0',
        gt_rxcdrhold_2    => '0',
        gt_rxcdrhold_3    => '0',
        gt_rxcommadeten_0 => '0',
        gt_rxcommadeten_1 => '0',
        gt_rxcommadeten_2 => '0',
        gt_rxcommadeten_3 => '0',
        gt_rxdfeagchold_0 => '0',
        gt_rxdfeagchold_1 => '0',
        gt_rxdfeagchold_2 => '0',
        gt_rxdfeagchold_3 => '0',
        gt_rxdfelpmreset_0 => '0',
        gt_rxdfelpmreset_1 => '0',
        gt_rxdfelpmreset_2 => '0',
        gt_rxdfelpmreset_3 => '0',
        gt_rxlatclk_0 => SYSCLK,
        gt_rxlatclk_1 => SYSCLK,
        gt_rxlatclk_2 => SYSCLK,
        gt_rxlatclk_3 => SYSCLK,
        gt_rxlpmen_0 => '0',
        gt_rxlpmen_1 => '0',
        gt_rxlpmen_2 => '0',
        gt_rxlpmen_3 => '0',
        gt_rxpcsreset_0 => '0',
        gt_rxpcsreset_1 => '0',
        gt_rxpcsreset_2 => '0',
        gt_rxpcsreset_3 => '0',
        gt_rxpmareset_0 => '0',
        gt_rxpmareset_1 => '0',
        gt_rxpmareset_2 => '0',
        gt_rxpmareset_3 => '0',
        gt_rxpolarity_0 => gt_rxpolarity(0),
        gt_rxpolarity_1 => gt_rxpolarity(1),
        gt_rxpolarity_2 => gt_rxpolarity(2),
        gt_rxpolarity_3 => gt_rxpolarity(3),
        gt_rxprbscntreset_0 => '0',
        gt_rxprbscntreset_1 => '0',
        gt_rxprbscntreset_2 => '0',
        gt_rxprbscntreset_3 => '0',
        gt_rxprbssel_0 => (others => '0'),
        gt_rxprbssel_1 => (others => '0'),
        gt_rxprbssel_2 => (others => '0'),
        gt_rxprbssel_3 => (others => '0'),
        gt_rxrate_0    => (others => '0'),
        gt_rxrate_1    => (others => '0'),
        gt_rxrate_2    => (others => '0'),
        gt_rxrate_3    => (others => '0'),
        gt_rxslide_in_0 => '0',
        gt_rxslide_in_1 => '0',
        gt_rxslide_in_2 => '0',
        gt_rxslide_in_3 => '0',
        gt_txdiffctrl_0 => gt_txdiffctrl((CH0_MAP+1)*5-1 downto CH0_MAP*5),
        gt_txdiffctrl_1 => gt_txdiffctrl((CH1_MAP+1)*5-1 downto CH1_MAP*5),
        gt_txdiffctrl_2 => gt_txdiffctrl((CH2_MAP+1)*5-1 downto CH2_MAP*5),
        gt_txdiffctrl_3 => gt_txdiffctrl((CH3_MAP+1)*5-1 downto CH3_MAP*5),
        gt_txinhibit_0 => '0',
        gt_txinhibit_1 => '0',
        gt_txinhibit_2 => '0',
        gt_txinhibit_3 => '0',
        gt_txlatclk_0  => SYSCLK,
        gt_txlatclk_1  => SYSCLK,
        gt_txlatclk_2  => SYSCLK,
        gt_txlatclk_3  => SYSCLK,
        gt_txmaincursor_0 => "1010000",
        gt_txmaincursor_1 => "1010000",
        gt_txmaincursor_2 => "1010000",
        gt_txmaincursor_3 => "1010000",
        gt_txpcsreset_0 => '0',
        gt_txpcsreset_1 => '0',
        gt_txpcsreset_2 => '0',
        gt_txpcsreset_3 => '0',
        gt_txpmareset_0 => '0',
        gt_txpmareset_1 => '0',
        gt_txpmareset_2 => '0',
        gt_txpmareset_3 => '0',
        gt_txpolarity_0 => gt_txpolarity(0),
        gt_txpolarity_1 => gt_txpolarity(1),
        gt_txpolarity_2 => gt_txpolarity(2),
        gt_txpolarity_3 => gt_txpolarity(3),
        gt_txpostcursor_0 => gt_postcursor((CH0_MAP+1)*5-1 downto CH0_MAP*5),
        gt_txpostcursor_1 => gt_postcursor((CH1_MAP+1)*5-1 downto CH1_MAP*5),
        gt_txpostcursor_2 => gt_postcursor((CH2_MAP+1)*5-1 downto CH2_MAP*5),
        gt_txpostcursor_3 => gt_postcursor((CH3_MAP+1)*5-1 downto CH3_MAP*5),
        gt_txprbsforceerr_0 => '0',
        gt_txprbsforceerr_1 => '0',
        gt_txprbsforceerr_2 => '0',
        gt_txprbsforceerr_3 => '0',
        gt_txprbssel_0 => (others => '0'),
        gt_txprbssel_1 => (others => '0'),
        gt_txprbssel_2 => (others => '0'),
        gt_txprbssel_3 => (others => '0'),
        gt_txprecursor_0 => gt_precursor((CH0_MAP+1)*5-1 downto CH0_MAP*5),
        gt_txprecursor_1 => gt_precursor((CH1_MAP+1)*5-1 downto CH1_MAP*5),
        gt_txprecursor_2 => gt_precursor((CH2_MAP+1)*5-1 downto CH2_MAP*5),
        gt_txprecursor_3 => gt_precursor((CH3_MAP+1)*5-1 downto CH3_MAP*5),

        gt_rxprbslocked_0 => open,
        gt_rxprbslocked_1 => open,
        gt_rxprbslocked_2 => open,
        gt_rxprbslocked_3 => open,
        gt_txresetdone_0  => open,
        gt_txresetdone_1  => open,
        gt_txresetdone_2  => open,
        gt_txresetdone_3  => open,
        gt_txelecidle_0   => (others =>'0'),
        gt_txelecidle_1   => (others =>'0'),
        gt_txelecidle_2   => (others =>'0'),
        gt_txelecidle_3   => (others =>'0'),
        qpllreset_in_0    => '0',
        --
        gt_drpclk_0 => SYSCLK,
        gt_drpclk_1 => SYSCLK,
        gt_drpclk_2 => SYSCLK,
        gt_drpclk_3 => SYSCLK,
        gt_drprst_0 => RESET,
        gt_drprst_1 => RESET,
        gt_drprst_2 => RESET,
        gt_drprst_3 => RESET,
        gt_drpdo_0 => open,
        gt_drpdo_1 => open,
        gt_drpdo_2 => open,
        gt_drpdo_3 => open,
        gt_drprdy_0 => open,
        gt_drprdy_1 => open,
        gt_drprdy_2 => open,
        gt_drprdy_3 => open,
        gt_drpen_0 => '0',
        gt_drpen_1 => '0',
        gt_drpen_2 => '0',
        gt_drpen_3 => '0',
        gt_drpwe_0 => '0',
        gt_drpwe_1 => '0',
        gt_drpwe_2 => '0',
        gt_drpwe_3 => '0',
        gt_drpaddr_0 => (others => '0'),
        gt_drpaddr_1 => (others => '0'),
        gt_drpaddr_2 => (others => '0'),
        gt_drpaddr_3 => (others => '0'),
        gt_drpdi_0   => (others => '0'),
        gt_drpdi_1   => (others => '0'),
        gt_drpdi_2   => (others => '0'),
        gt_drpdi_3   => (others => '0'),
        --
        rx_mii_d_0 => eth0_rxd((CH0_MAP+1)*64-1 downto CH0_MAP*64),
        rx_mii_c_0 => eth0_rxc((CH0_MAP+1)*8-1 downto CH0_MAP*8),
        rx_mii_d_1 => eth0_rxd((CH1_MAP+1)*64-1 downto CH1_MAP*64),
        rx_mii_c_1 => eth0_rxc((CH1_MAP+1)*8-1 downto CH1_MAP*8),
        rx_mii_d_2 => eth0_rxd((CH2_MAP+1)*64-1 downto CH2_MAP*64),
        rx_mii_c_2 => eth0_rxc((CH2_MAP+1)*8-1 downto CH2_MAP*8),
        rx_mii_d_3 => eth0_rxd((CH3_MAP+1)*64-1 downto CH3_MAP*64),
        rx_mii_c_3 => eth0_rxc((CH3_MAP+1)*8-1 downto CH3_MAP*8),

        -- -
        ctl_rx_test_pattern_0 => '0',
        ctl_rx_test_pattern_1 => '0',
        ctl_rx_test_pattern_2 => '0',
        ctl_rx_test_pattern_3 => '0',
        ctl_rx_data_pattern_select_0 => '0',
        ctl_rx_data_pattern_select_1 => '0',
        ctl_rx_data_pattern_select_2 => '0',
        ctl_rx_data_pattern_select_3 => '0',
        ctl_rx_test_pattern_enable_0 => '0',
        ctl_rx_test_pattern_enable_1 => '0',
        ctl_rx_test_pattern_enable_2 => '0',
        ctl_rx_test_pattern_enable_3 => '0',
        ctl_rx_prbs31_test_pattern_enable_0 => '0',
        ctl_rx_prbs31_test_pattern_enable_1 => '0',
        ctl_rx_prbs31_test_pattern_enable_2 => '0',
        ctl_rx_prbs31_test_pattern_enable_3 => '0',

        stat_rx_framing_err_0 => framing_err(CH0_MAP), -- Bad sync header => generate BER counter
        stat_rx_framing_err_1 => framing_err(CH1_MAP),
        stat_rx_framing_err_2 => framing_err(CH2_MAP),
        stat_rx_framing_err_3 => framing_err(CH3_MAP),
        stat_rx_framing_err_valid_0 => framing_err_vld(CH0_MAP),
        stat_rx_framing_err_valid_1 => framing_err_vld(CH1_MAP),
        stat_rx_framing_err_valid_2 => framing_err_vld(CH2_MAP),
        stat_rx_framing_err_valid_3 => framing_err_vld(CH3_MAP),

        stat_rx_local_fault_0 => TX_LOCAL_FAULT(CH0_MAP),
        stat_rx_local_fault_1 => TX_LOCAL_FAULT(CH1_MAP),
        stat_rx_local_fault_2 => TX_LOCAL_FAULT(CH2_MAP),
        stat_rx_local_fault_3 => TX_LOCAL_FAULT(CH3_MAP),
        --
        stat_rx_block_lock_0  => blk_lock(CH0_MAP),
        stat_rx_block_lock_1  => blk_lock(CH1_MAP),
        stat_rx_block_lock_2  => blk_lock(CH2_MAP),
        stat_rx_block_lock_3  => blk_lock(CH3_MAP),
        stat_rx_valid_ctrl_code_0 => open,
        stat_rx_valid_ctrl_code_1 => open,
        stat_rx_valid_ctrl_code_2 => open,
        stat_rx_valid_ctrl_code_3 => open,
        stat_rx_status_0 => link_status(CH0_MAP),
        stat_rx_status_1 => link_status(CH1_MAP),
        stat_rx_status_2 => link_status(CH2_MAP),
        stat_rx_status_3 => link_status(CH3_MAP),
        stat_rx_hi_ber_0 => hi_ber(CH0_MAP),
        stat_rx_hi_ber_1 => hi_ber(CH1_MAP),
        stat_rx_hi_ber_2 => hi_ber(CH2_MAP),
        stat_rx_hi_ber_3 => hi_ber(CH3_MAP),
        stat_rx_bad_code_0 => bad_code(CH0_MAP), -- Generate errored_block_count - r3.33 7:0
        stat_rx_bad_code_1 => bad_code(CH1_MAP),
        stat_rx_bad_code_2 => bad_code(CH2_MAP),
        stat_rx_bad_code_3 => bad_code(CH3_MAP),
        stat_rx_bad_code_valid_0 => bad_code_vld(CH0_MAP),
        stat_rx_bad_code_valid_1 => bad_code_vld(CH1_MAP),
        stat_rx_bad_code_valid_2 => bad_code_vld(CH2_MAP),
        stat_rx_bad_code_valid_3 => bad_code_vld(CH3_MAP),
        stat_rx_error_0 => open,
        stat_rx_error_1 => open,
        stat_rx_error_2 => open,
        stat_rx_error_3 => open,
        stat_rx_error_valid_0 => open,
        stat_rx_error_valid_1 => open,
        stat_rx_error_valid_2 => open,
        stat_rx_error_valid_3 => open,
        stat_rx_fifo_error_0 => open,
        stat_rx_fifo_error_1 => open,
        stat_rx_fifo_error_2 => open,
        stat_rx_fifo_error_3 => open,
        tx_reset_0 => eth0_txreset(CH0_MAP),
        tx_reset_1 => eth0_txreset(CH1_MAP),
        tx_reset_2 => eth0_txreset(CH2_MAP),
        tx_reset_3 => eth0_txreset(CH3_MAP),
        user_tx_reset_0 => TXRESET(CH0_MAP),
        user_tx_reset_1 => TXRESET(CH1_MAP),
        user_tx_reset_2 => TXRESET(CH2_MAP),
        user_tx_reset_3 => TXRESET(CH3_MAP),
        ---
        tx_mii_d_0 => TXD((CH0_MAP+1)*64-1 downto CH0_MAP*64),
        tx_mii_d_1 => TXD((CH1_MAP+1)*64-1 downto CH1_MAP*64),
        tx_mii_d_2 => TXD((CH2_MAP+1)*64-1 downto CH2_MAP*64),
        tx_mii_d_3 => TXD((CH3_MAP+1)*64-1 downto CH3_MAP*64),
        tx_mii_c_0 => TXC((CH0_MAP+1)*8-1 downto CH0_MAP*8),
        tx_mii_c_1 => TXC((CH1_MAP+1)*8-1 downto CH1_MAP*8),
        tx_mii_c_2 => TXC((CH2_MAP+1)*8-1 downto CH2_MAP*8),
        tx_mii_c_3 => TXC((CH3_MAP+1)*8-1 downto CH3_MAP*8),
        --
        stat_tx_local_fault_0 => open,
        stat_tx_local_fault_1 => open,
        stat_tx_local_fault_2 => open,
        stat_tx_local_fault_3 => open,
        ctl_tx_test_pattern_0 => '0',
        ctl_tx_test_pattern_1 => '0',
        ctl_tx_test_pattern_2 => '0',
        ctl_tx_test_pattern_3 => '0',
        ctl_tx_test_pattern_enable_0 => '0',
        ctl_tx_test_pattern_enable_1 => '0',
        ctl_tx_test_pattern_enable_2 => '0',
        ctl_tx_test_pattern_enable_3 => '0',
        ctl_tx_test_pattern_select_0 => '0',
        ctl_tx_test_pattern_select_1 => '0',
        ctl_tx_test_pattern_select_2 => '0',
        ctl_tx_test_pattern_select_3 => '0',
        ctl_tx_data_pattern_select_0 => '0',
        ctl_tx_data_pattern_select_1 => '0',
        ctl_tx_data_pattern_select_2 => '0',
        ctl_tx_data_pattern_select_3 => '0',
        ctl_tx_test_pattern_seed_a_0 => (others => '0'),
        ctl_tx_test_pattern_seed_a_1 => (others => '0'),
        ctl_tx_test_pattern_seed_a_2 => (others => '0'),
        ctl_tx_test_pattern_seed_a_3 => (others => '0'),
        ctl_tx_test_pattern_seed_b_0 => (others => '0'),
        ctl_tx_test_pattern_seed_b_1 => (others => '0'),
        ctl_tx_test_pattern_seed_b_2 => (others => '0'),
        ctl_tx_test_pattern_seed_b_3 => (others => '0'),
        ctl_tx_prbs31_test_pattern_enable_0 => '0',
        ctl_tx_prbs31_test_pattern_enable_1 => '0',
        ctl_tx_prbs31_test_pattern_enable_2 => '0',
        ctl_tx_prbs31_test_pattern_enable_3 => '0',
        gt_loopback_in_0 => gt_loopback((CH0_MAP+1)*3-1 downto CH0_MAP*3),
        gt_loopback_in_1 => gt_loopback((CH1_MAP+1)*3-1 downto CH1_MAP*3),
        gt_loopback_in_2 => gt_loopback((CH2_MAP+1)*3-1 downto CH2_MAP*3),
        gt_loopback_in_3 => gt_loopback((CH3_MAP+1)*3-1 downto CH3_MAP*3)
    );

    ber_cntr_clk <= eth0_core_clk;
    blk_cntr_clk <= eth0_core_clk;

end generate;

---------------------------------------------------------------------------
--  25 Gig Ethe PCS/PMA core
---------------------------------------------------------------------------

GEN_25GE: if ETH_25G generate

    ETH25G_I :  twenty_five_gig_eth_pcspma
    PORT MAP (
        sys_reset     => RESET,
        dclk          => SYSCLK,
        --
        gt_rxp_in_0   => RX_P(0),
        gt_rxp_in_1   => RX_P(1),
        gt_rxp_in_2   => RX_P(2),
        gt_rxp_in_3   => RX_P(3),
        --
        gt_rxn_in_0   => RX_N(0),
        gt_rxn_in_1   => RX_N(1),
        gt_rxn_in_2   => RX_N(2),
        gt_rxn_in_3   => RX_N(3),
        --
        gt_txp_out_0  => TX_P(0),
        gt_txp_out_1  => TX_P(1),
        gt_txp_out_2  => TX_P(2),
        gt_txp_out_3  => TX_P(3),
        --
        gt_txn_out_0  => TX_N(0),
        gt_txn_out_1  => TX_N(1),
        gt_txn_out_2  => TX_N(2),
        gt_txn_out_3  => TX_N(3),
        --
        rx_core_clk_0 => eth0_clk(CH0_MAP), -- eth0_core_clk(0),
        rx_core_clk_1 => eth0_clk(CH1_MAP), -- eth0_core_clk(1),
        rx_core_clk_2 => eth0_clk(CH2_MAP), -- eth0_core_clk(2),
        rx_core_clk_3 => eth0_clk(CH3_MAP), -- eth0_core_clk(3),

        --
        gtwiz_reset_tx_datapath_0 => eth0_pma_txreset(CH0_MAP),
        gtwiz_reset_tx_datapath_1 => eth0_pma_txreset(CH1_MAP),
        gtwiz_reset_tx_datapath_2 => eth0_pma_txreset(CH2_MAP),
        gtwiz_reset_tx_datapath_3 => eth0_pma_txreset(CH3_MAP),
        --
        gtwiz_reset_rx_datapath_0 => eth0_pma_rxreset(CH0_MAP),
        gtwiz_reset_rx_datapath_1 => eth0_pma_rxreset(CH1_MAP),
        gtwiz_reset_rx_datapath_2 => eth0_pma_rxreset(CH2_MAP),
        gtwiz_reset_rx_datapath_3 => eth0_pma_rxreset(CH3_MAP),
        rxrecclkout_0 => open,
        rxrecclkout_1 => open,
        rxrecclkout_2 => open,
        rxrecclkout_3 => open,
        tx_mii_clk_0 => eth0_clk(CH0_MAP), -- txusrclk2
        tx_mii_clk_1 => eth0_clk(CH1_MAP), -- txusrclk2
        tx_mii_clk_2 => eth0_clk(CH2_MAP), -- txusrclk2
        tx_mii_clk_3 => eth0_clk(CH3_MAP), -- txusrclk2
        rx_clk_out_0 => eth0_core_clk(CH0_MAP), -- rxusrclk2
        rx_clk_out_1 => eth0_core_clk(CH1_MAP), -- rxusrclk2
        rx_clk_out_2 => eth0_core_clk(CH2_MAP), -- rxusrclk2
        rx_clk_out_3 => eth0_core_clk(CH3_MAP), -- rxusrclk2
        gt_refclk_p => REFCLK_P,
        gt_refclk_n => REFCLK_N,
        gt_refclk_out => open,

        gtpowergood_out_0 => open,
        gtpowergood_out_1 => open,
        gtpowergood_out_2 => open,
        gtpowergood_out_3 => open,
        rx_reset_0 => eth0_rxreset(CH0_MAP),
        rx_reset_1 => eth0_rxreset(CH1_MAP),
        rx_reset_2 => eth0_rxreset(CH2_MAP),
        rx_reset_3 => eth0_rxreset(CH3_MAP),
        user_rx_reset_0 => eth0_rx_usr_rst(CH0_MAP), -- RXRESET(CH0_MAP), -- (gt_rxresetdone OR rx_reset), synchronous with rx_core_clk
        user_rx_reset_1 => eth0_rx_usr_rst(CH1_MAP), -- RXRESET(CH1_MAP),
        user_rx_reset_2 => eth0_rx_usr_rst(CH2_MAP), -- RXRESET(CH2_MAP),
        user_rx_reset_3 => eth0_rx_usr_rst(CH3_MAP), -- RXRESET(CH3_MAP),
        --
        txoutclksel_in_0 => "101",
        txoutclksel_in_1 => "101",
        txoutclksel_in_2 => "101",
        txoutclksel_in_3 => "101",
        rxoutclksel_in_0 => "101",
        rxoutclksel_in_1 => "101",
        rxoutclksel_in_2 => "101",
        rxoutclksel_in_3 => "101",
        --
        gt_eyescanreset_0 => '0',
        gt_eyescanreset_1 => '0',
        gt_eyescanreset_2 => '0',
        gt_eyescanreset_3 => '0',
        gt_eyescantrigger_0 => '0',
        gt_eyescantrigger_1 => '0',
        gt_eyescantrigger_2 => '0',
        gt_eyescantrigger_3 => '0',
        gt_pcsrsvdin_0 => (others => '0'),
        gt_pcsrsvdin_1 => (others => '0'),
        gt_pcsrsvdin_2 => (others => '0'),
        gt_pcsrsvdin_3 => (others => '0'),
        gt_rxbufreset_0 => '0',
        gt_rxbufreset_1 => '0',
        gt_rxbufreset_2 => '0',
        gt_rxbufreset_3 => '0',
        gt_rxcdrhold_0    => '0',
        gt_rxcdrhold_1    => '0',
        gt_rxcdrhold_2    => '0',
        gt_rxcdrhold_3    => '0',
        gt_rxcommadeten_0 => '0',
        gt_rxcommadeten_1 => '0',
        gt_rxcommadeten_2 => '0',
        gt_rxcommadeten_3 => '0',
        gt_rxdfeagchold_0 => '0',
        gt_rxdfeagchold_1 => '0',
        gt_rxdfeagchold_2 => '0',
        gt_rxdfeagchold_3 => '0',
        gt_rxdfelpmreset_0 => '0',
        gt_rxdfelpmreset_1 => '0',
        gt_rxdfelpmreset_2 => '0',
        gt_rxdfelpmreset_3 => '0',
        gt_rxlatclk_0 => SYSCLK,
        gt_rxlatclk_1 => SYSCLK,
        gt_rxlatclk_2 => SYSCLK,
        gt_rxlatclk_3 => SYSCLK,
        gt_rxlpmen_0 => '0',
        gt_rxlpmen_1 => '0',
        gt_rxlpmen_2 => '0',
        gt_rxlpmen_3 => '0',
        gt_rxpcsreset_0 => '0',
        gt_rxpcsreset_1 => '0',
        gt_rxpcsreset_2 => '0',
        gt_rxpcsreset_3 => '0',
        gt_rxpmareset_0 => '0',
        gt_rxpmareset_1 => '0',
        gt_rxpmareset_2 => '0',
        gt_rxpmareset_3 => '0',
        gt_rxpolarity_0 => gt_rxpolarity(0),
        gt_rxpolarity_1 => gt_rxpolarity(1),
        gt_rxpolarity_2 => gt_rxpolarity(2),
        gt_rxpolarity_3 => gt_rxpolarity(3),
        gt_rxprbscntreset_0 => '0',
        gt_rxprbscntreset_1 => '0',
        gt_rxprbscntreset_2 => '0',
        gt_rxprbscntreset_3 => '0',
        gt_rxprbssel_0 => (others => '0'),
        gt_rxprbssel_1 => (others => '0'),
        gt_rxprbssel_2 => (others => '0'),
        gt_rxprbssel_3 => (others => '0'),
        gt_rxrate_0    => (others => '0'),
        gt_rxrate_1    => (others => '0'),
        gt_rxrate_2    => (others => '0'),
        gt_rxrate_3    => (others => '0'),
        gt_rxslide_in_0 => '0',
        gt_rxslide_in_1 => '0',
        gt_rxslide_in_2 => '0',
        gt_rxslide_in_3 => '0',
        gt_txdiffctrl_0 => gt_txdiffctrl((CH0_MAP+1)*5-1 downto CH0_MAP*5),
        gt_txdiffctrl_1 => gt_txdiffctrl((CH1_MAP+1)*5-1 downto CH1_MAP*5),
        gt_txdiffctrl_2 => gt_txdiffctrl((CH2_MAP+1)*5-1 downto CH2_MAP*5),
        gt_txdiffctrl_3 => gt_txdiffctrl((CH3_MAP+1)*5-1 downto CH3_MAP*5),
        gt_txinhibit_0 => '0',
        gt_txinhibit_1 => '0',
        gt_txinhibit_2 => '0',
        gt_txinhibit_3 => '0',
        gt_txlatclk_0  => SYSCLK,
        gt_txlatclk_1  => SYSCLK,
        gt_txlatclk_2  => SYSCLK,
        gt_txlatclk_3  => SYSCLK,
        gt_txmaincursor_0 => "1010000",
        gt_txmaincursor_1 => "1010000",
        gt_txmaincursor_2 => "1010000",
        gt_txmaincursor_3 => "1010000",
        gt_txpcsreset_0 => '0',
        gt_txpcsreset_1 => '0',
        gt_txpcsreset_2 => '0',
        gt_txpcsreset_3 => '0',
        gt_txpmareset_0 => '0',
        gt_txpmareset_1 => '0',
        gt_txpmareset_2 => '0',
        gt_txpmareset_3 => '0',
        gt_txpolarity_0 => gt_txpolarity(0),
        gt_txpolarity_1 => gt_txpolarity(1),
        gt_txpolarity_2 => gt_txpolarity(2),
        gt_txpolarity_3 => gt_txpolarity(3),
        gt_txpostcursor_0 => gt_postcursor((CH0_MAP+1)*5-1 downto CH0_MAP*5),
        gt_txpostcursor_1 => gt_postcursor((CH1_MAP+1)*5-1 downto CH1_MAP*5),
        gt_txpostcursor_2 => gt_postcursor((CH2_MAP+1)*5-1 downto CH2_MAP*5),
        gt_txpostcursor_3 => gt_postcursor((CH3_MAP+1)*5-1 downto CH3_MAP*5),
        gt_txprbsforceerr_0 => '0',
        gt_txprbsforceerr_1 => '0',
        gt_txprbsforceerr_2 => '0',
        gt_txprbsforceerr_3 => '0',
        gt_txprbssel_0 => (others => '0'),
        gt_txprbssel_1 => (others => '0'),
        gt_txprbssel_2 => (others => '0'),
        gt_txprbssel_3 => (others => '0'),
        gt_txprecursor_0 => gt_precursor((CH0_MAP+1)*5-1 downto CH0_MAP*5),
        gt_txprecursor_1 => gt_precursor((CH1_MAP+1)*5-1 downto CH1_MAP*5),
        gt_txprecursor_2 => gt_precursor((CH2_MAP+1)*5-1 downto CH2_MAP*5),
        gt_txprecursor_3 => gt_precursor((CH3_MAP+1)*5-1 downto CH3_MAP*5),

        gt_rxprbslocked_0 => open,
        gt_rxprbslocked_1 => open,
        gt_rxprbslocked_2 => open,
        gt_rxprbslocked_3 => open,
        gt_txresetdone_0  => open,
        gt_txresetdone_1  => open,
        gt_txresetdone_2  => open,
        gt_txresetdone_3  => open,
        gt_txelecidle_0   => (others =>'0'),
        gt_txelecidle_1   => (others =>'0'),
        gt_txelecidle_2   => (others =>'0'),
        gt_txelecidle_3   => (others =>'0'),
        qpllreset_in_0    => '0',
        --
        gt_drpclk_0 => SYSCLK,
        gt_drpclk_1 => SYSCLK,
        gt_drpclk_2 => SYSCLK,
        gt_drpclk_3 => SYSCLK,
        gt_drprst_0 => RESET,
        gt_drprst_1 => RESET,
        gt_drprst_2 => RESET,
        gt_drprst_3 => RESET,
        gt_drpdo_0 => drpdo(CH0_MAP*16+15 downto CH0_MAP*16),
        gt_drpdo_1 => drpdo(CH1_MAP*16+15 downto CH1_MAP*16),
        gt_drpdo_2 => drpdo(CH2_MAP*16+15 downto CH2_MAP*16),
        gt_drpdo_3 => drpdo(CH3_MAP*16+15 downto CH3_MAP*16),
        gt_drprdy_0 => drprdy(CH0_MAP),
        gt_drprdy_1 => drprdy(CH1_MAP),
        gt_drprdy_2 => drprdy(CH2_MAP),
        gt_drprdy_3 => drprdy(CH3_MAP),
        gt_drpen_0 => drpen(CH0_MAP),
        gt_drpen_1 => drpen(CH1_MAP),
        gt_drpen_2 => drpen(CH2_MAP),
        gt_drpen_3 => drpen(CH3_MAP),
        gt_drpwe_0 => drpwe(CH0_MAP),
        gt_drpwe_1 => drpwe(CH1_MAP),
        gt_drpwe_2 => drpwe(CH2_MAP),
        gt_drpwe_3 => drpwe(CH3_MAP),
        gt_drpaddr_0 => drpaddr(CH0_MAP*16+9 downto CH0_MAP*16),
        gt_drpaddr_1 => drpaddr(CH1_MAP*16+9 downto CH1_MAP*16),
        gt_drpaddr_2 => drpaddr(CH2_MAP*16+9 downto CH2_MAP*16),
        gt_drpaddr_3 => drpaddr(CH3_MAP*16+9 downto CH3_MAP*16),
        gt_drpdi_0   => drpdi(CH0_MAP*16+15 downto CH0_MAP*16),
        gt_drpdi_1   => drpdi(CH1_MAP*16+15 downto CH1_MAP*16),
        gt_drpdi_2   => drpdi(CH2_MAP*16+15 downto CH2_MAP*16),
        gt_drpdi_3   => drpdi(CH3_MAP*16+15 downto CH3_MAP*16),
        --
        rx_mii_d_0 => eth0_rxd((CH0_MAP+1)*64-1 downto CH0_MAP*64),
        rx_mii_c_0 => eth0_rxc((CH0_MAP+1)*8-1 downto CH0_MAP*8),
        rx_mii_d_1 => eth0_rxd((CH1_MAP+1)*64-1 downto CH1_MAP*64),
        rx_mii_c_1 => eth0_rxc((CH1_MAP+1)*8-1 downto CH1_MAP*8),
        rx_mii_d_2 => eth0_rxd((CH2_MAP+1)*64-1 downto CH2_MAP*64),
        rx_mii_c_2 => eth0_rxc((CH2_MAP+1)*8-1 downto CH2_MAP*8),
        rx_mii_d_3 => eth0_rxd((CH3_MAP+1)*64-1 downto CH3_MAP*64),
        rx_mii_c_3 => eth0_rxc((CH3_MAP+1)*8-1 downto CH3_MAP*8),

        -- -
        ctl_rx_test_pattern_0 => '0',
        ctl_rx_test_pattern_1 => '0',
        ctl_rx_test_pattern_2 => '0',
        ctl_rx_test_pattern_3 => '0',
        ctl_rx_data_pattern_select_0 => '0',
        ctl_rx_data_pattern_select_1 => '0',
        ctl_rx_data_pattern_select_2 => '0',
        ctl_rx_data_pattern_select_3 => '0',
        ctl_rx_test_pattern_enable_0 => '0',
        ctl_rx_test_pattern_enable_1 => '0',
        ctl_rx_test_pattern_enable_2 => '0',
        ctl_rx_test_pattern_enable_3 => '0',
        ctl_rx_prbs31_test_pattern_enable_0 => '0',
        ctl_rx_prbs31_test_pattern_enable_1 => '0',
        ctl_rx_prbs31_test_pattern_enable_2 => '0',
        ctl_rx_prbs31_test_pattern_enable_3 => '0',

        stat_rx_framing_err_0 => framing_err(CH0_MAP), -- Bad sync header => generate BER counter
        stat_rx_framing_err_1 => framing_err(CH1_MAP),
        stat_rx_framing_err_2 => framing_err(CH2_MAP),
        stat_rx_framing_err_3 => framing_err(CH3_MAP),
        stat_rx_framing_err_valid_0 => framing_err_vld(CH0_MAP),
        stat_rx_framing_err_valid_1 => framing_err_vld(CH1_MAP),
        stat_rx_framing_err_valid_2 => framing_err_vld(CH2_MAP),
        stat_rx_framing_err_valid_3 => framing_err_vld(CH3_MAP),

        stat_rx_local_fault_0 => open,
        stat_rx_local_fault_1 => open,
        stat_rx_local_fault_2 => open,
        stat_rx_local_fault_3 => open,
        --
        stat_rx_block_lock_0  => blk_lock(CH0_MAP),
        stat_rx_block_lock_1  => blk_lock(CH1_MAP),
        stat_rx_block_lock_2  => blk_lock(CH2_MAP),
        stat_rx_block_lock_3  => blk_lock(CH3_MAP),
        stat_rx_valid_ctrl_code_0 => open,
        stat_rx_valid_ctrl_code_1 => open,
        stat_rx_valid_ctrl_code_2 => open,
        stat_rx_valid_ctrl_code_3 => open,
        stat_rx_status_0 => link_status(CH0_MAP),
        stat_rx_status_1 => link_status(CH1_MAP),
        stat_rx_status_2 => link_status(CH2_MAP),
        stat_rx_status_3 => link_status(CH3_MAP),
        stat_rx_hi_ber_0 => hi_ber(CH0_MAP),
        stat_rx_hi_ber_1 => hi_ber(CH1_MAP),
        stat_rx_hi_ber_2 => hi_ber(CH2_MAP),
        stat_rx_hi_ber_3 => hi_ber(CH3_MAP),
        stat_rx_bad_code_0 => bad_code(CH0_MAP), -- Generate errored_block_count - r3.33 7:0
        stat_rx_bad_code_1 => bad_code(CH1_MAP),
        stat_rx_bad_code_2 => bad_code(CH2_MAP),
        stat_rx_bad_code_3 => bad_code(CH3_MAP),
        stat_rx_bad_code_valid_0 => bad_code_vld(CH0_MAP),
        stat_rx_bad_code_valid_1 => bad_code_vld(CH1_MAP),
        stat_rx_bad_code_valid_2 => bad_code_vld(CH2_MAP),
        stat_rx_bad_code_valid_3 => bad_code_vld(CH3_MAP),
        stat_rx_error_0 => open,
        stat_rx_error_1 => open,
        stat_rx_error_2 => open,
        stat_rx_error_3 => open,
        stat_rx_error_valid_0 => open,
        stat_rx_error_valid_1 => open,
        stat_rx_error_valid_2 => open,
        stat_rx_error_valid_3 => open,
        stat_rx_fifo_error_0 => open,
        stat_rx_fifo_error_1 => open,
        stat_rx_fifo_error_2 => open,
        stat_rx_fifo_error_3 => open,
        tx_reset_0 => eth0_txreset(CH0_MAP),
        tx_reset_1 => eth0_txreset(CH1_MAP),
        tx_reset_2 => eth0_txreset(CH2_MAP),
        tx_reset_3 => eth0_txreset(CH3_MAP),
        user_tx_reset_0 => TXRESET(CH0_MAP),
        user_tx_reset_1 => TXRESET(CH1_MAP),
        user_tx_reset_2 => TXRESET(CH2_MAP),
        user_tx_reset_3 => TXRESET(CH3_MAP),
        ---
        tx_mii_d_0 => TXD((CH0_MAP+1)*64-1 downto CH0_MAP*64),
        tx_mii_d_1 => TXD((CH1_MAP+1)*64-1 downto CH1_MAP*64),
        tx_mii_d_2 => TXD((CH2_MAP+1)*64-1 downto CH2_MAP*64),
        tx_mii_d_3 => TXD((CH3_MAP+1)*64-1 downto CH3_MAP*64),
        tx_mii_c_0 => TXC((CH0_MAP+1)*8-1 downto CH0_MAP*8),
        tx_mii_c_1 => TXC((CH1_MAP+1)*8-1 downto CH1_MAP*8),
        tx_mii_c_2 => TXC((CH2_MAP+1)*8-1 downto CH2_MAP*8),
        tx_mii_c_3 => TXC((CH3_MAP+1)*8-1 downto CH3_MAP*8),
        --
        stat_tx_local_fault_0 => TX_LOCAL_FAULT(CH0_MAP),
        stat_tx_local_fault_1 => TX_LOCAL_FAULT(CH1_MAP),
        stat_tx_local_fault_2 => TX_LOCAL_FAULT(CH2_MAP),
        stat_tx_local_fault_3 => TX_LOCAL_FAULT(CH3_MAP),
        ctl_tx_test_pattern_0 => '0',
        ctl_tx_test_pattern_1 => '0',
        ctl_tx_test_pattern_2 => '0',
        ctl_tx_test_pattern_3 => '0',
        ctl_tx_test_pattern_enable_0 => '0',
        ctl_tx_test_pattern_enable_1 => '0',
        ctl_tx_test_pattern_enable_2 => '0',
        ctl_tx_test_pattern_enable_3 => '0',
        ctl_tx_test_pattern_select_0 => '0',
        ctl_tx_test_pattern_select_1 => '0',
        ctl_tx_test_pattern_select_2 => '0',
        ctl_tx_test_pattern_select_3 => '0',
        ctl_tx_data_pattern_select_0 => '0',
        ctl_tx_data_pattern_select_1 => '0',
        ctl_tx_data_pattern_select_2 => '0',
        ctl_tx_data_pattern_select_3 => '0',
        ctl_tx_test_pattern_seed_a_0 => (others => '0'),
        ctl_tx_test_pattern_seed_a_1 => (others => '0'),
        ctl_tx_test_pattern_seed_a_2 => (others => '0'),
        ctl_tx_test_pattern_seed_a_3 => (others => '0'),
        ctl_tx_test_pattern_seed_b_0 => (others => '0'),
        ctl_tx_test_pattern_seed_b_1 => (others => '0'),
        ctl_tx_test_pattern_seed_b_2 => (others => '0'),
        ctl_tx_test_pattern_seed_b_3 => (others => '0'),
        ctl_tx_prbs31_test_pattern_enable_0 => '0',
        ctl_tx_prbs31_test_pattern_enable_1 => '0',
        ctl_tx_prbs31_test_pattern_enable_2 => '0',
        ctl_tx_prbs31_test_pattern_enable_3 => '0',
        gt_loopback_in_0 => gt_loopback((CH0_MAP+1)*3-1 downto CH0_MAP*3),
        gt_loopback_in_1 => gt_loopback((CH1_MAP+1)*3-1 downto CH1_MAP*3),
        gt_loopback_in_2 => gt_loopback((CH2_MAP+1)*3-1 downto CH2_MAP*3),
        gt_loopback_in_3 => gt_loopback((CH3_MAP+1)*3-1 downto CH3_MAP*3)
    );

    ber_cntr_clk(3 downto 0) <= eth0_clk(3 downto 0);
    blk_cntr_clk(3 downto 0) <= eth0_clk(3 downto 0);

end generate;


XGCLK <= eth0_clk;

RXRESET <= eth0_rxreset;
--RXRESET <= eth0_rx_usr_rst;

MGMT_GEN: for i in 0 to 3 generate
    signal gt_precursor_mgmt          : std_logic_vector(31 downto 0);
    signal gt_postcursor_mgmt         : std_logic_vector(31 downto 0);
    signal gt_txdiffctrl_mgmt         : std_logic_vector(31 downto 0);
begin

    -- Indicate local fault to XGMII when the PCS/PMA is reset
    RXD(64*(i+1)-1 downto 64*i) <= X"0100009C0100009C" when eth0_rx_usr_rst(i) = '1' else
                                   eth0_rxd(64*(i+1)-1 downto 64*i);
    RXC( 8*(i+1)-1 downto  8*i) <= "00010001"          when eth0_rx_usr_rst(i) = '1' else
                                   eth0_rxc( 8*(i+1)-1 downto  8*i);

    -- Synchronize PCS reset to the eth0_clk domain
    SYNC_PCS_TXRST: entity work.ASYNC_RESET
    generic map(TWO_REG => false)
    port map(
        CLK        => eth0_clk(i),
        ASYNC_RST  => eth0_txreset_a(i),
        OUT_RST(0) => eth0_txreset(i)
    );

    -- Synchronize PCS reset to the eth0_clk domain
    SYNC_PCS_RXRST: entity work.ASYNC_RESET
    generic map(TWO_REG => false)
    port map(
        CLK        => eth0_clk(i),
        ASYNC_RST  => eth0_rxreset_a(i),
        OUT_RST(0) => eth0_rxreset(i)
    );

    -- Synchronize BER_MONITOR reset to the eth0_clk domain
    SYNC_BERMONITOR_RST: entity work.ASYNC_RESET
    generic map(TWO_REG => false)
    port map(
        CLK        => ber_cntr_clk(i),
        ASYNC_RST  => RESET,
        OUT_RST(0) => ber_mon_reset(i)
    );

    eth0_txreset_a(i) <= RESET or pcs_reset(i);
    eth0_rxreset_a(i) <= RESET or pcs_reset(i);
    eth0_pma_txreset(i) <= RESET or pma_reset(i);
    eth0_pma_rxreset(i) <= RESET or pma_reset(i) or rx_link_rst(i);

    sync_ber_mon_clr: entity work.ASYNC_OPEN_LOOP
    generic map(IN_REG  => false, TWO_REG => true)
    port map( ADATAIN  => ber_cnt_clr(i), BCLK => ber_cntr_clk(i), BDATAOUT => ber_cnt_clr_sync(i));

    -- BER monitor
    ber_mon_sh((i+1)*2-1 downto i*2) <= "00" when framing_err(i) = '1' else "01";
    BER_MONITOR: entity work.ber_mon
    generic map (
       NUM_LANES       => 1
    )
    port map (
        RESET         => ber_mon_reset(i),
        CLK           => ber_cntr_clk(i),
        CE            => framing_err_vld(i),
        SH            => ber_mon_sh((i+1)*2-1 downto i*2),
        --
        BER_CNT       => open,
        BER_COUNT_CLR => ber_cnt_clr_sync(i),
        BER_COUNT     => ber_count((i+1)*22-1 downto i*22),
        HI_BER        => open
    );

    sync_blk_err_clr: entity work.ASYNC_OPEN_LOOP
    generic map(IN_REG  => false, TWO_REG => true)
    port map ( ADATAIN  => blk_err_clr(i), BCLK => blk_cntr_clk(i), BDATAOUT => blk_err_clr_sync(i) );

    BLK_ERR_COUNTERS: process(blk_cntr_clk(i))
    begin
        if blk_cntr_clk(i)'event and blk_cntr_clk(i) = '1' then
            if (ber_mon_reset(i) = '1') or (blk_err_clr_sync(i) = '1') then
                blk_err_cntr(22*(i+1)-1 downto 22*i) <= (others => '0');
            elsif (bad_code(i) = '1') and (bad_code_vld(i) = '1') then
                if (blk_err_cntr(22*(i+1)-1 downto 22*i) /= "1111111111111111111111") then
                    blk_err_cntr(22*(i+1)-1 downto 22*i) <= std_logic_vector(unsigned(blk_err_cntr(22*(i+1)-1 downto 22*i)) + to_unsigned(1, 22));
                end if;
            end if;
        end if;
    end process;

    gt_loopback((i+1)*3-1 downto i*3)
        <= "100" when (pma_lpbck(i) = '0') and (pma_rem_lpbck(i) = '1') else  -- Far end PMA loopback
           "010" when (pma_lpbck(i) = '1') and (pma_rem_lpbck(i) = '0') else  -- Near end PMA loopback
           "000";
    -- Disable polarity swaps when the local loopback is active
    gt_rxpolarity_async(CH_MAP(i)) <= '0' when gt_loopback(i*3+1) = '1' else RXPOLARITY(CH_MAP(i));
    gt_txpolarity_async(CH_MAP(i)) <= '0' when gt_loopback(i*3+1) = '1' else TXPOLARITY(CH_MAP(i));

    rxpol_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map(IN_REG  => false, TWO_REG => true)
        port map(ADATAIN  => gt_rxpolarity_async(i), BCLK => eth0_core_clk(i), BRST => '0', BDATAOUT => gt_rxpolarity(i)
    );

    txpol_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map(IN_REG  => false, TWO_REG => true)
        port map(ADATAIN  => gt_txpolarity_async(i), BCLK => eth0_clk(i), BRST => '0', BDATAOUT => gt_txpolarity(i)
    );

    MGMT_I: entity work.mgmt
    generic map (
        NUM_LANES => 1,
        PMA_LANES => 1,
        RSFEC_ABLE=> '0',
        SPEED     => C_SPEED_SEL(ETH_25G),
        SPEED_CAP => C_CAP_SEL(ETH_25G),
        PMA_DRIVE_INIT      => X"000000"&"000"& GTY_TX_EQ((i+1)*5+00-1 downto i*5+00),
        PMA_PRECURSOR_INIT  => X"000000"&"000"& GTY_TX_EQ((i+1)*5+20-1 downto i*5+20),
        PMA_POSTCURSOR_INIT => X"000000"&"000"& GTY_TX_EQ((i+1)*5+40-1 downto i*5+40)
    )
    port map (
        RESET    => RESET,
        MI_CLK   => MI_CLK,
        MI_DWR   => mi_split_dwr(i),
        MI_ADDR  => mi_split_addr(i),
        MI_RD    => mi_split_rd(i),
        MI_WR    => mi_split_wr(i),
        MI_BE    => mi_split_be(i),
        MI_DRD   => mi_split_drd(i),
        MI_ARDY  => mi_split_ardy(i),
        MI_DRDY  => mi_split_drdy(i),
        -- PMA & PMD status/control
        PMA_LPBCK     => pma_lpbck(i),
        PMA_REM_LPBCK => pma_rem_lpbck(i),
        PMA_RESET     => pma_reset(i),
        PMA_RETUNE    => open,
        PMA_RX_OK     => blk_lock(i downto i),
        PMD_SIG_DET   => SIGNAL_DETECT(i downto i),
        PMA_PRECURSOR => gt_precursor_mgmt,
        PMA_POSTCURSOR=> gt_postcursor_mgmt,
        PMA_DRIVE     => gt_txdiffctrl_mgmt,
        -- PCS Lane align
        ALGN_LOCKED   => '1',
        LANE_MAP      => (others => '0'),
        LANE_ALIGN    => (others => '0'),
        BIP_ERR_CNTRS => (others => '0'),
        BIP_ERR_CLR   => open,
        -- PCS status
        HI_BER        => hi_ber(i),
        BLK_LOCK      => blk_lock(i downto i),
        LINKSTATUS    => link_status(i),
        BER_COUNT     => ber_count((i+1)*22-1 downto i*22),
        BER_COUNT_CLR => ber_cnt_clr(i),
        BLK_ERR_CNTR  => blk_err_cntr((i+1)*22-1 downto i*22),
        BLK_ERR_CLR   => blk_err_clr(i),
        SCR_BYPASS    => open,
        PCS_RESET     => pcs_reset(i),
        PCS_LPBCK     => open,
        --
        -- DRP interface for GT's
        DRPCLK            => SYSCLK,
        DRPDO             => drpdo(i*16+15 downto i*16),
        DRPRDY            => drprdy(i),
        DRPEN             => drpen(i),
        DRPWE             => drpwe(i),
        DRPADDR           => drpaddr(i*16+15 downto i*16),
        DRPDI             => drpdi(i*16+15 downto i*16),
        DRPSEL            => open
    );

    gt_precursor((i+1)*5-1 downto i*5)  <= gt_precursor_mgmt(4 downto 0);
    gt_postcursor((i+1)*5-1 downto i*5) <= gt_postcursor_mgmt(4 downto 0);
    gt_txdiffctrl((i+1)*5-1 downto i*5) <= gt_txdiffctrl_mgmt(4 downto 0);

    sync_link_stat: entity work.ASYNC_OPEN_LOOP
    generic map(IN_REG  => false, TWO_REG => true)
    port map( ADATAIN  => link_status(i), BCLK => eth0_core_clk(i), BDATAOUT => link_status_sync(i));

    -- counter for monitoring link state - resets RX data path when link down
    LINK_MON: process(eth0_core_clk(i))
    begin
        if eth0_core_clk(i)'event and eth0_core_clk(i) = '1' then
            -- Wait 100 ms for the link to become active. If not, reset the RX PMA
            if (link_status_sync(i) = '1') or (rx_link_rst(i) = '1') then
                -- link is up, clear the counter
                link_cntr((i+1)*LINKSTAT_CNTR_LENGTH-1 downto i*LINKSTAT_CNTR_LENGTH) <= (others => '0');
            else
                -- link is down, increase the counter. When its last bit is set, reset the link
                link_cntr((i+1)*LINKSTAT_CNTR_LENGTH-1 downto i*LINKSTAT_CNTR_LENGTH) <= std_logic_vector(unsigned(link_cntr((i+1)*LINKSTAT_CNTR_LENGTH-1 downto i*LINKSTAT_CNTR_LENGTH)) + to_unsigned(1, LINKSTAT_CNTR_LENGTH));
            end if;
            rx_link_rst(i) <= link_cntr((i+1)*LINKSTAT_CNTR_LENGTH-1);
        end if;
    end process;

end generate;

    -- -------------------------------------------------------------------------
    --                               MI Splitter
    -- -------------------------------------------------------------------------
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
        DEVICE      => "ULTRASCALE"
    )
    port map(
        CLK     => MI_CLK,
        RESET   => RESET,

        RX_DWR  => MI_DWR,
        RX_MWR  => (others => '0'),
        RX_ADDR => MI_ADDR,
        RX_BE   => MI_BE,
        RX_RD   => MI_RD,
        RX_WR   => MI_WR,
        RX_ARDY => MI_ARDY,
        RX_DRD  => MI_DRD,
        RX_DRDY => MI_DRDY,

        TX_DWR  => mi_split_dwr,
        TX_MWR  => open,
        TX_ADDR => mi_split_addr,
        TX_BE   => mi_split_be,
        TX_RD   => mi_split_rd,
        TX_WR   => mi_split_wr,
        TX_ARDY => mi_split_ardy,
        TX_DRD  => mi_split_drd,
        TX_DRDY => mi_split_drdy
    );

end architecture;

