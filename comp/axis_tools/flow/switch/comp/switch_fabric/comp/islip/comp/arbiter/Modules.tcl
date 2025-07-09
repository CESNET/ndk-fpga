# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

lappend COMPONENTS [ list "PRIORITY_ENC"  "$ENTITY_BASE/../priority_enc"     "FULL" ]
lappend COMPONENTS [ list "DEC1FN_ENABLE" "$OFM_PATH/comp/base/logic/dec1fn" "FULL" ]

lappend MOD "$ENTITY_BASE/arbiter.vhd"
