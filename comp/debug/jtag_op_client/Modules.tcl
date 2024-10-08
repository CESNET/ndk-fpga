# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MI2AVMM_BASE  "$OFM_PATH/comp/mi_tools/converters/mi2avmm"
set MI_ASYNC_BASE "$OFM_PATH/comp/mi_tools/async"

lappend COMPONENTS [ list "MI2AVMM"  $MI2AVMM_BASE  "FULL" ]
lappend COMPONENTS [ list "MI_ASYNC" $MI_ASYNC_BASE "FULL" ]

lappend MOD "$ENTITY_BASE/jtag_op_client.vhd"

lappend MOD "$ENTITY_BASE/DevTree.tcl"
