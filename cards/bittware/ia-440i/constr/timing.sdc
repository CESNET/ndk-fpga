# timing.sdc: Timing constraints
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

derive_clock_uncertainty

create_clock -name {altera_reserved_tck} -period 41.667 [get_ports { altera_reserved_tck }]

create_clock -name {SYS_CLK_100M}        -period 10.000 [get_ports { SYS_CLK_100M }]
create_clock -name {PCIE_REFCLK0}        -period 10.000 [get_ports { PCIE_REFCLK0 }]
create_clock -name {PCIE_REFCLK1}        -period 10.000 [get_ports { PCIE_REFCLK1 }]
create_clock -name {QSFP_REFCLK_156M}    -period 6.400  [get_ports { QSFP_REFCLK_156M }]

# Cut (set_false_path) this JTAG clock from all other clocks in the design
set_clock_groups -asynchronous -group [get_clocks altera_reserved_tck]

set MI_CLK [get_clocks cm_i|clk_gen_i|iopll_i|iopll_0_outclk3]

# the only supported configuration so far!
set FHIP_400G_CLK [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_1x400g8_g.eth_ip_g[0].ftile_1x400g8_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch23]

# Fix hold timing issues on FHIP
set_clock_groups -asynchronous -group $MI_CLK -group $FHIP_400G_CLK
