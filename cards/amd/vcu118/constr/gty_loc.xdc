# qsfp.xdc
# Copyright (C) 2023 CESNET z.s.p.o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set_property LOC CMACE4_X0Y8 [get_cells -hierarchical -filter {NAME =~ *eth_core_g[1].network_mod_core_i/cmac_eth_1x100g_i/* && REF_NAME==CMACE4}]
set_property LOC GTYE4_CHANNEL_X0Y52 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[1]*" && NAME =~ "*channel_inst[0]*" }]
set_property LOC GTYE4_CHANNEL_X0Y53 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[1]*" && NAME =~ "*channel_inst[1]*" }]
set_property LOC GTYE4_CHANNEL_X0Y54 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[1]*" && NAME =~ "*channel_inst[2]*" }]
set_property LOC GTYE4_CHANNEL_X0Y55 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[1]*" && NAME =~ "*channel_inst[3]*" }]

set_property LOC CMACE4_X0Y7 [get_cells -hierarchical -filter {NAME =~ *eth_core_g[0].network_mod_core_i/cmac_eth_1x100g_i/* && REF_NAME==CMACE4}]
set_property LOC GTYE4_CHANNEL_X1Y48 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[0]*" && NAME =~ "*channel_inst[0]*" }]
set_property LOC GTYE4_CHANNEL_X1Y49 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[0]*" && NAME =~ "*channel_inst[1]*" }]
set_property LOC GTYE4_CHANNEL_X1Y50 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[0]*" && NAME =~ "*channel_inst[2]*" }]
set_property LOC GTYE4_CHANNEL_X1Y51 [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*eth_core_g[0]*" && NAME =~ "*channel_inst[3]*" }]
