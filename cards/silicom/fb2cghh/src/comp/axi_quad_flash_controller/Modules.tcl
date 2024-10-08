# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2022 CESNET
# Author: David Beneš <benes.david2000@seznam.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths
set AXI4_LITE_MI_BRIDGE_BASE    "$ENTITY_BASE/comp/axi4_lite_mi_bridge/"

# Components
lappend COMPONENTS [list "AXI4_LITE_MI_BRIDGE"    $AXI4_LITE_MI_BRIDGE_BASE  "FULL"]

# Files
lappend MOD "$ENTITY_BASE/axi_quad_flash_controller.vhd"