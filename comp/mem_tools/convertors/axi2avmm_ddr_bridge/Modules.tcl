# Modules.tcl: Components include script
# Copyright (C) 2017 CESNET
# Author(s): David Beneš <xbenes52@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set AXI2AVMM_BRIDGE_BASE "$OFM_PATH/comp/mem_tools/convertors/axi2avmm_ddr_bridge"

lappend PACKAGES  "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES  "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [list "AXI2AVMM_BRIDGE" $AXI2AVMM_BRIDGE_BASE "FULL"]

lappend MOD "$ENTITY_BASE/axi2avmm_ddr_bridge.vhd"
