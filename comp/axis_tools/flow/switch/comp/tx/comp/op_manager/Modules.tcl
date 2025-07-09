# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "AXIS_VOQ_MANAGER" "$ENTITY_BASE/../../../rx/comp/voq_manager"                   "FULL" ]
lappend COMPONENTS [ list "DEC1FN_ENABLE"    "$OFM_PATH/comp/base/logic/dec1fn"                            "FULL" ]
lappend COMPONENTS [ list "ARBITER"          "$ENTITY_BASE/../../../switch_fabric/comp/islip/comp/arbiter" "FULL" ]
lappend COMPONENTS [ list "GEN_ENC"          "$OFM_PATH/comp/base/logic/enc"                               "FULL" ]

lappend MOD "$ENTITY_BASE/op_manager.vhd"
