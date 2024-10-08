# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set JTAG_OP_CLIENT_BASE "$OFM_PATH/comp/debug/jtag_op_client"

lappend MOD "$ENTITY_BASE/jtag_op_ctrl_ent.vhd"

if {$ARCHGRP == "INTEL"} {
    lappend COMPONENTS [ list "JTAG_OP_CLIENT" $JTAG_OP_CLIENT_BASE "FULL" ]

    lappend MOD "$ENTITY_BASE/jtag_op_ctrl_arch.vhd"
} else {
    lappend MOD "$ENTITY_BASE/jtag_op_ctrl_empty.vhd"
}
