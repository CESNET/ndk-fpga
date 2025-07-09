# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

lappend COMPONENTS [ list "BARREL_BIT_SHIFTER" "$OFM_PATH/comp/base/logic/barrel_shifter" "FULL" ]
lappend COMPONENTS [ list "FIRST_ONE"          "$OFM_PATH/comp/base/logic/first_one"      "FULL" ]
lappend COMPONENTS [ list "DEC1FN2B"           "$OFM_PATH/comp/base/logic/dec1fn"         "FULL" ]

lappend MOD "$ENTITY_BASE/priority_enc.vhd"
