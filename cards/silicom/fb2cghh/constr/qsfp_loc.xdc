# qsfp_loc.xdc
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# ==============================================================================
# LOC locations for CMAC interfaces
# ==============================================================================
#

set_property LOC CMACE4_X0Y1 [get_cells -hierarchical -filter {NAME =~ *eth_core_g[0].network_mod_core_i/cmac_eth_1x100g_i/* && REF_NAME==CMACE4}]
set_property LOC GTYE4_CHANNEL_X0Y12 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[0]*" && NAME =~ "*channel_inst[0]*" }]
set_property LOC GTYE4_CHANNEL_X0Y13 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[0]*" && NAME =~ "*channel_inst[1]*" }]
set_property LOC GTYE4_CHANNEL_X0Y14 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[0]*" && NAME =~ "*channel_inst[2]*" }]
set_property LOC GTYE4_CHANNEL_X0Y15 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[0]*" && NAME =~ "*channel_inst[3]*" }]

set_property LOC CMACE4_X0Y2 [get_cells -hierarchical -filter {NAME =~ *eth_core_g[1].network_mod_core_i/cmac_eth_1x100g_i/* && REF_NAME==CMACE4}]
set_property LOC GTYE4_CHANNEL_X0Y20 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[1]*" && NAME =~ "*channel_inst[0]*" }]
set_property LOC GTYE4_CHANNEL_X0Y21 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[1]*" && NAME =~ "*channel_inst[1]*" }]
set_property LOC GTYE4_CHANNEL_X0Y22 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[1]*" && NAME =~ "*channel_inst[2]*" }]
set_property LOC GTYE4_CHANNEL_X0Y23 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[1]*" && NAME =~ "*channel_inst[3]*" }]

