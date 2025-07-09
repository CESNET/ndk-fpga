# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$ENTITY_BASE/../comp/pkg/proto_hdr_pack.vhd"
lappend PACKAGES "$ENTITY_BASE/../comp/pkg/proto_match_pack.vhd"
lappend PACKAGES "$ENTITY_BASE/../comp/pkg/config_pack.vhd"

lappend COMPONENTS [ list "AXIS_RX_PIPELINE"   "$ENTITY_BASE/../comp/rx"                 "FULL" ]
lappend COMPONENTS [ list "AXIS_SWITCH_FABRIC" "$ENTITY_BASE/../comp/switch_fabric/"     "FULL" ]
lappend COMPONENTS [ list "AXIS_OP_MANAGER"    "$ENTITY_BASE/../comp/tx/comp/op_manager" "FULL" ]
lappend COMPONENTS [ list "SWITCH_CONTROLLER"  "$ENTITY_BASE/../comp/ctrl"               "FULL" ]

lappend MOD "$ENTITY_BASE/switch.vhd"
