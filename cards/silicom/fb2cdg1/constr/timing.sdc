# timing.sdc: Timing constraints
# Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

derive_clock_uncertainty

# From Timequest cookbook
set_clock_groups -exclusive -group [get_clocks altera_reserved_tck]

set_input_delay  -clock altera_reserved_tck -clock_fall 3 [get_ports altera_reserved_tdi]
set_input_delay  -clock altera_reserved_tck -clock_fall 3 [get_ports altera_reserved_tms]
set_output_delay -clock altera_reserved_tck             3 [get_ports altera_reserved_tdo]

create_clock -name {altera_reserved_tck} -period 40 [get_ports {altera_reserved_tck}]
# Cut (set_false_path) this JTAG clock from all other clocks in the design
set_clock_groups -asynchronous -group [get_clocks altera_reserved_tck]

create_clock -name {SYSCLK}    -period 10.000 [get_ports {   SYSCLK_100_P }]
create_clock -name {PCIE_CLK0} -period 10.000 [get_ports {    PCIE_CLK0_P }]
create_clock -name {PCIE_CLK1} -period 10.000 [get_ports {    PCIE_CLK1_P }]
create_clock -name {QSFP_CLK0} -period  6.400 [get_ports { QSFP0_REFCLK_P }]
create_clock -name {QSFP_CLK1} -period  6.400 [get_ports { QSFP1_REFCLK_P }]

# ===========
# Global clks
# ===========
set MI_CLK_CH3  [get_clocks ag_i|clk_gen_i|iopll_i|iopll_0_outclk3]

# ============
# 400G2 design
# ============
set FHIP_400G2_P0_CLK_CH23 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_1x400g8_g.eth_ip_g[0].FTILE_1x400g8_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch23]
set FHIP_400G2_P1_CLK_CH23 [get_clocks ag_i|network_mod_i|eth_core_g[1].network_mod_core_i|ftile_1x400g8_g.eth_ip_g[0].FTILE_1x400g8_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch23]

# Fix hold timing issues for 400G2 design
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_400G2_P0_CLK_CH23
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_400G2_P1_CLK_CH23
