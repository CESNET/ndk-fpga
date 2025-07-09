# Modules.tcl: Components include script
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$ENTITY_BASE/../../../pkg/proto_hdr_pack.vhd"

lappend COMPONENTS [ list "AXIS_HDR_EXTRACT" "$OFM_PATH/comp/axis_tools/flow/hdr_extract" "FULL" ]

lappend MOD "$ENTITY_BASE/parser.vhd"
