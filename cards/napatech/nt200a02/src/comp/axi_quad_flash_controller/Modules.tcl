# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2025 DynaNIC Semiconductors s.r.o.
# Author(s): Jan Privara <privara@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths
set AXI4_LITE_MI_BRIDGE_BASE "$ENTITY_BASE/../../../../../silicom/fb2cghh/src/comp/axi_quad_flash_controller/comp/axi4_lite_mi_bridge"

# Components
lappend COMPONENTS [list "AXI4_LITE_MI_BRIDGE" $AXI4_LITE_MI_BRIDGE_BASE  "FULL"]

# Files
lappend MOD "$ENTITY_BASE/axi_quad_flash_controller.vhd"
