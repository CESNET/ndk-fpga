# gty_loc.xdc
# Copyright (C) 2025 DynaNIC Semiconductors s.r.o.
# Author(s): Jan Privara <privara@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# ==============================================================================
# LOC locations for CMAC interfaces
# ==============================================================================

set_property LOC CMACE4_X0Y4 [get_cells -hierarchical -filter {NAME =~ *eth_core_g[0].network_mod_core_i/cmac_eth_1x100g_i/* && REF_NAME==CMACE4}]
set_property LOC GTYE4_CHANNEL_X0Y28 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[0]*" && NAME =~ "*channel_inst[0]*" }]
set_property LOC GTYE4_CHANNEL_X0Y29 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[0]*" && NAME =~ "*channel_inst[1]*" }]
set_property LOC GTYE4_CHANNEL_X0Y30 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[0]*" && NAME =~ "*channel_inst[2]*" }]
set_property LOC GTYE4_CHANNEL_X0Y31 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[0]*" && NAME =~ "*channel_inst[3]*" }]

set_property LOC CMACE4_X0Y5 [get_cells -hierarchical -filter {NAME =~ *eth_core_g[1].network_mod_core_i/cmac_eth_1x100g_i/* && REF_NAME==CMACE4}]
set_property LOC GTYE4_CHANNEL_X0Y32 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[1]*" && NAME =~ "*channel_inst[0]*" }]
set_property LOC GTYE4_CHANNEL_X0Y33 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[1]*" && NAME =~ "*channel_inst[1]*" }]
set_property LOC GTYE4_CHANNEL_X0Y34 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[1]*" && NAME =~ "*channel_inst[2]*" }]
set_property LOC GTYE4_CHANNEL_X0Y35 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[1]*" && NAME =~ "*channel_inst[3]*" }]
