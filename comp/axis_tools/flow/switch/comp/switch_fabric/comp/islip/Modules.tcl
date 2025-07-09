# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "ARBITER" "$ENTITY_BASE/comp/arbiter" "FULL" ]

lappend MOD "$ENTITY_BASE/islip_iteration.vhd"
lappend MOD "$ENTITY_BASE/islip.vhd"
