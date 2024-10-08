# gty_10ge_ll.xdc
# Copyright (C) 2024 CESNET z.s.p.o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# 10GE LL mode only: redefine settings for 161 MHz reference clock
set_property QPLL0_CFG2 16'h87C0 [get_cells {usp_i/network_mod_i/eth_core_g[?].network_mod_core_i/ll_4x10ge_g.eth_phy_i/pma_i/gtye4_common_i/common_inst/gtye4_common_gen.GTYE4_COMMON_PRIM_INST}]
set_property QPLL0_CFG2_G3 16'h87C0 [get_cells {usp_i/network_mod_i/eth_core_g[?].network_mod_core_i/ll_4x10ge_g.eth_phy_i/pma_i/gtye4_common_i/common_inst/gtye4_common_gen.GTYE4_COMMON_PRIM_INST}]
set_property QPLL0_FBDIV 64 [get_cells {usp_i/network_mod_i/eth_core_g[?].network_mod_core_i/ll_4x10ge_g.eth_phy_i/pma_i/gtye4_common_i/common_inst/gtye4_common_gen.GTYE4_COMMON_PRIM_INST}]
set_property QPLL0_LPF 10'b1000111111 [get_cells {usp_i/network_mod_i/eth_core_g[?].network_mod_core_i/ll_4x10ge_g.eth_phy_i/pma_i/gtye4_common_i/common_inst/gtye4_common_gen.GTYE4_COMMON_PRIM_INST}]
