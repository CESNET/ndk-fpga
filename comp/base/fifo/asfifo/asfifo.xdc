# asfifo.xdc: Local constrains for ASFIFO
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# This constrains will be applied everytime.
set wr_clk [get_clocks -of_objects [get_ports CLK_WR]]
set rd_clk [get_clocks -of_objects [get_ports CLK_RD]]
set_max_delay -from $wr_clk -to [get_cells reg_rd_data_reg[*]] -datapath_only [get_property PERIOD $rd_clk]

