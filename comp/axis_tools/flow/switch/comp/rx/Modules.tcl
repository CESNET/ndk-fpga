# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$ENTITY_BASE/../pkg/proto_hdr_pack.vhd"
lappend PACKAGES "$ENTITY_BASE/../pkg/proto_match_pack.vhd"

lappend COMPONENTS [ list "AXIS_PARSER"      "$ENTITY_BASE/comp/parser"      "FULL" ]
lappend COMPONENTS [ list "AXIS_DISPATCHER"  "$ENTITY_BASE/comp/dispatcher"  "FULL" ]
lappend COMPONENTS [ list "AXIS_VOQ_MANAGER" "$ENTITY_BASE/comp/voq_manager" "FULL" ]

lappend MOD "$ENTITY_BASE/rx_pipeline.vhd"
