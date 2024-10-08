# timing.sdc: Timing constraints
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

derive_clock_uncertainty

create_clock -period 40.0 -name {altera_reserved_tck} [get_ports {altera_reserved_tck}]
create_clock -period 30.0 -name {clk_usr_33m}         [get_ports {USR_CLK_33M}]
create_clock -period 6.4  -name {clk_qsfp_156m}       [get_ports {QSFP_REFCLK_156M}]
create_clock -period 10.0 -name {clk_pcie_refclk0}    [get_ports {PCIE_REFCLK0}]
create_clock -period 10.0 -name {clk_pcie_refclk1}    [get_ports {PCIE_REFCLK1}]
create_clock -period 30.0 -name {clk_ddr4_ch0_33m}    [get_ports {DDR4_CH0_REFCLK_P}]
create_clock -period 30.0 -name {clk_ddr4_ch1_33m}    [get_ports {DDR4_CH1_REFCLK_P}]

# ==============================================================================

create_clock -name {BMC2FPGA_SPI_SCK} -period 200.0 [get_ports BMC2FPGA_SPI_SCK]

set_input_delay -clock BMC2FPGA_SPI_SCK -max 10.0 [get_ports {BMC2FPGA_SPI_MOSI}]
set_input_delay -clock BMC2FPGA_SPI_SCK -min 0.0  [get_ports {BMC2FPGA_SPI_MOSI}]
set_input_delay -clock BMC2FPGA_SPI_SCK -max 10.0 [get_ports {BMC2FPGA_SPI_CS}]
set_input_delay -clock BMC2FPGA_SPI_SCK -min 0.0  [get_ports {BMC2FPGA_SPI_CS}]

set_output_delay -clock BMC2FPGA_SPI_SCK -max 12.0 [get_ports {BMC2FPGA_SPI_MISO}]
set_output_delay -clock BMC2FPGA_SPI_SCK -min 1.0  [get_ports {BMC2FPGA_SPI_MISO}]

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
