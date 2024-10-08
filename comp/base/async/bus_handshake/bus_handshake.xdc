# bus_handshake.xdc: Local Vivado constrains
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# This constrains will be applied everytime.

set dst_clk [get_clocks -of_objects [get_ports BCLK]]
set_max_delay -from [get_cells adata_reg[*]] -to [get_cells bdata_reg[*]*] -datapath_only [get_property PERIOD $dst_clk]

