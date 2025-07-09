# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

lappend COMPONENTS [ list "ISLIP"         "$ENTITY_BASE/comp/islip"                  "FULL" ]
lappend COMPONENTS [ list "AXIS_CROSSBAR" "$OFM_PATH/comp/axis_tools/logic/crossbar" "FULL" ]

lappend MOD "$ENTITY_BASE/switch_fabric.vhd"
