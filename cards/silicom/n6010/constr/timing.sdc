# timing.sdc: Timing constraints
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Martin Matějka <xmatej55@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

derive_clock_uncertainty

#create_clock -period 40.0 -name {altera_reserved_tck} [get_ports {altera_reserved_tck}]
create_clock -period 10.0 -name {clk_sys_100m}        [get_ports {SYS_CLK_100M}]
create_clock -period 40.0 -name {spi_egress_sclk}     [get_ports {SPI_EGRESS_SCLK}]
create_clock -period 10.0 -name {clk_pcie_refclk0}    [get_ports {PCIE_REFCLK0}]
create_clock -period 10.0 -name {clk_pcie_refclk1}    [get_ports {PCIE_REFCLK1}]

# TODO DDR clock

# ==============================================================================

set MI_CLK [get_clocks cm_i|clk_gen_i|iopll_i|iopll_0_outclk3]
set OSC_CLK [get_clocks ALTERA_INSERTED_INTOSC_FOR_TRS|divided_osc_clk]
set TCK_CLK [get_clocks altera_reserved_tck]

set EHIP100G_CORE0_CLK [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_fm_0|alt_ehipc3_fm_hard_inst|E100GX4_FEC.altera_xcvr_native_inst|xcvr_native_s10_etile_0_example_design_4ln_ptp|tx_clkout|ch0]
set EHIP100G_CORE1_CLK [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_fm_0|alt_ehipc3_fm_hard_inst|E100GX4_FEC.altera_xcvr_native_inst|xcvr_native_s10_etile_0_example_design_4ln_ptp|tx_clkout|ch0]

set EHIP25G_CORE0_CLK0 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch0]
set EHIP25G_CORE0_CLK1 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch1]
set EHIP25G_CORE0_CLK2 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch2]
set EHIP25G_CORE0_CLK3 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch3]

set EHIP25G_CORE1_CLK0 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch0]
set EHIP25G_CORE1_CLK1 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch1]
set EHIP25G_CORE1_CLK2 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch2]
set EHIP25G_CORE1_CLK3 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY_RSFEC.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch3]

set EHIP10G_CORE0_CLK0 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch0]
set EHIP10G_CORE0_CLK1 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch1]
set EHIP10G_CORE0_CLK2 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch2]
set EHIP10G_CORE0_CLK3 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch3]

set EHIP10G_CORE1_CLK0 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch0]
set EHIP10G_CORE1_CLK1 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch1]
set EHIP10G_CORE1_CLK2 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch2]
set EHIP10G_CORE1_CLK3 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_*0|alt_ehipc3_*hard_inst|SL_NPHY.altera_xcvr_native_inst|alt_ehipc3_*nphy_elane|tx_clkout|ch3]

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

# ==============================================================================
