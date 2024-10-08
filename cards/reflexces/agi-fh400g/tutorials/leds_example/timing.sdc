# timing.sdc: Timing constraints
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

derive_clock_uncertainty

# ==============================================================================
# Create Clock constraints
# ==============================================================================

#create_clock -name {altera_reserved_tck} -period 41.667 [get_ports { altera_reserved_tck }]
#set_clock_groups -asynchronous -group [get_clocks {altera_reserved_tck}]

#create_clock -name {PCIE0_CLK0} -period "100MHz" [get_ports { PCIE0_CLK0_P }]
#create_clock -name {PCIE0_CLK1} -period "100MHz" [get_ports { PCIE0_CLK1_P }]
#create_clock -name {PCIE1_CLK0} -period "100MHz" [get_ports { PCIE1_CLK0_P }]
#create_clock -name {PCIE1_CLK1} -period "100MHz" [get_ports { PCIE1_CLK1_P }]
#create_clock -name {PCIE2_CLK0} -period "100MHz" [get_ports { PCIE2_CLK0_P }]
#create_clock -name {PCIE2_CLK1} -period "100MHz" [get_ports { PCIE2_CLK1_P }]
#create_clock -name {QSFP_REFCLK_P} -period "644.53125MHz" [get_ports { QSFP_REFCLK_P }]
