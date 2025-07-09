# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

lappend COMPONENTS [ list "TCAM2"           "$OFM_PATH/comp/base/mem/tcam2"      "FULL" ]
lappend COMPONENTS [ list "GEN_ENC"         "$OFM_PATH/comp/base/logic/enc"      "FULL" ]
lappend COMPONENTS [ list "GEN_LUTRAM"      "$OFM_PATH/comp/base/mem/gen_lutram" "FULL" ]

lappend MOD "$ENTITY_BASE/match_action_table.vhd"
