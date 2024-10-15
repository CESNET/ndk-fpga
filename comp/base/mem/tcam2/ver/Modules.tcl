# Modules.tcl: Local include tcl script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SV_MVB_BASE "$OFM_PATH/comp/mvb_tools/ver"
set SV_WB_BASE  "$ENTITY_BASE/tbench/write_bus"
set SV_RB_BASE  "$ENTITY_BASE/tbench/read_bus"

lappend COMPONENTS [ list "SV_MVB" $SV_MVB_BASE "FULL" ]
lappend COMPONENTS [ list "SV_WB"  $SV_WB_BASE  "FULL" ]
lappend COMPONENTS [ list "SV_RB"  $SV_RB_BASE  "FULL" ]

lappend MOD "$ENTITY_BASE/tbench/test_pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/test.sv"
