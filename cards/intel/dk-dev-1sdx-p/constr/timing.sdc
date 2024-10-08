# timing.sdc: Timing constraints
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

derive_clock_uncertainty

create_clock -period 40.0 -name {altera_reserved_tck} [get_ports {altera_reserved_tck}]
create_clock -period 10.0 -name {fpga_sysclk0_100m}   [get_ports {FPGA_SYSCLK0_100M_P}]
create_clock -period 3.2  -name {clk_312p5m_qsfp0}    [get_ports {CLK_312P5M_QSFP0_P}]
create_clock -period 6.4  -name {clk_156p25m_qsfp0}   [get_ports {CLK_156P25M_QSFP0_P}]
create_clock -period 3.2  -name {clk_312p5m_qsfp1}    [get_ports {CLK_312P5M_QSFP1_P}]
create_clock -period 6.4  -name {clk_156p25m_qsfp1}   [get_ports {CLK_156P25M_QSFP1_P}]
create_clock -period 3.2  -name {clk_312p5m_qsfp2}    [get_ports {CLK_312P5M_QSFP2_P}]
create_clock -period 7.5  -name {clk_133m_dimm_0}     [get_ports {CLK_133M_DIMM_0_P}]
create_clock -period 7.5  -name {clk_133m_dimm_1}     [get_ports {CLK_133M_DIMM_1_P}]

set MI_CLK [get_clocks cm_i|clk_gen_i|iopll_i|iopll_0_outclk3]
set OSC_CLK [get_clocks ALTERA_INSERTED_INTOSC_FOR_TRS|divided_osc_clk]
set TCK_CLK [get_clocks altera_reserved_tck]
set EMIF0_CLK [get_clocks s10_emif_ip_ch0_i|emif_s10_0_core_cal_master_clk]
set EMIF1_CLK [get_clocks s10_emif_ip_ch1_i|emif_s10_0_core_cal_master_clk]

set EHIP100G_CORE0_CLK [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|E100GX4_FEC.altera_xcvr_native_inst|xcvr_native_s10_etile_0_example_design_4ln_ptp|tx_clkout|ch0]
set EHIP100G_CORE1_CLK [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|E100GX4_FEC.altera_xcvr_native_inst|xcvr_native_s10_etile_0_example_design_4ln_ptp|tx_clkout|ch0]

set EHIP25G_CORE0_CLK0 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch0]
set EHIP25G_CORE0_CLK1 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch1]
set EHIP25G_CORE0_CLK2 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch2]
set EHIP25G_CORE0_CLK3 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch3]

set EHIP25G_CORE1_CLK0 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch0]
set EHIP25G_CORE1_CLK1 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch1]
set EHIP25G_CORE1_CLK2 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch2]
set EHIP25G_CORE1_CLK3 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch3]

set EHIP10G_CORE0_CLK0 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch0]
set EHIP10G_CORE0_CLK1 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch1]
set EHIP10G_CORE0_CLK2 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch2]
set EHIP10G_CORE0_CLK3 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch3]

set EHIP10G_CORE1_CLK0 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch0]
set EHIP10G_CORE1_CLK1 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch1]
set EHIP10G_CORE1_CLK2 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch2]
set EHIP10G_CORE1_CLK3 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_nphy_elane|tx_clkout|ch3]

# Fix hold timing issues on EHIP
set_clock_groups -asynchronous -group $MI_CLK -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP100G_CORE0_CLK -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP100G_CORE1_CLK -group $OSC_CLK

set_clock_groups -asynchronous -group $MI_CLK -group $EHIP10G_CORE0_CLK0 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP10G_CORE0_CLK1 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP10G_CORE0_CLK2 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP10G_CORE0_CLK3 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP10G_CORE1_CLK0 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP10G_CORE1_CLK1 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP10G_CORE1_CLK2 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP10G_CORE1_CLK3 -group $OSC_CLK

set_clock_groups -asynchronous -group $MI_CLK -group $EHIP25G_CORE0_CLK0 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP25G_CORE0_CLK1 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP25G_CORE0_CLK2 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP25G_CORE0_CLK3 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP25G_CORE1_CLK0 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP25G_CORE1_CLK1 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP25G_CORE1_CLK2 -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP25G_CORE1_CLK3 -group $OSC_CLK

set_false_path -to cm_i|network_mod_i|eth_core_g[*].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|RST_CTRL_100G.alt_ehipc3_reset_controller_inst|rx_reset_synchronizers|resync_chains[0].synchronizer_nocut|din_s1
set_false_path -to cm_i|network_mod_i|eth_core_g[*].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|RST_CTRL_100G.alt_ehipc3_reset_controller_inst|tx_reset_synchronizers|resync_chains[0].synchronizer_nocut|din_s1
set_false_path -to cm_i|network_mod_i|eth_core_g[*].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|RST_CTRL_100G.alt_ehipc3_reset_controller_inst|ehip_rst_seqinst|rxpfa_synchronizers|resync_chains[0].synchronizer_nocut|din_s1

# Fix recovery timing issues on EMIF
set_clock_groups -asynchronous -group $TCK_CLK -group $EMIF0_CLK
set_clock_groups -asynchronous -group $TCK_CLK -group $EMIF1_CLK
