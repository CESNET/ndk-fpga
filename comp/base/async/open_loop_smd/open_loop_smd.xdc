# open_loop_smd.xdc: Local constrains for ASYNC_OPEN_LOOP_SMD
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set src_clk [get_clocks -of_objects [get_ports ACLK]]

set_max_delay -from [get_cells input_reg_reg[*]] -to [get_cells sync1_reg_reg[*]] -datapath_only [get_property PERIOD $src_clk]

# Some other constraints are applied as attributes directly in VHDL code.
