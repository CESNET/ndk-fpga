# Modules.tcl: Components include script
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$ENTITY_BASE/../../../pkg/proto_hdr_pack.vhd"
lappend PACKAGES "$ENTITY_BASE/../../../pkg/proto_match_pack.vhd"
lappend PACKAGES "$ENTITY_BASE/../../../pkg/config_pack.vhd"

lappend COMPONENTS [ list "AXIS_FIFO"          "$OFM_PATH/comp/axis_tools/storage/fifo" "FULL" ]
lappend COMPONENTS [ list "MATCH_ACTION_TABLE" "$ENTITY_BASE/comp/match_action_table"   "FULL" ]
lappend COMPONENTS [ list "GEN_MUX_ONEHOT"     "$OFM_PATH/comp/base/logic/mux"          "FULL" ]
lappend COMPONENTS [ list "FIFOX"              "$OFM_PATH/comp/base/fifo/fifox"         "FULL" ]
lappend COMPONENTS [ list "RESOLVER"           "$ENTITY_BASE/comp/resolver"             "FULL" ]

lappend MOD "$ENTITY_BASE/dispatcher.vhd"
