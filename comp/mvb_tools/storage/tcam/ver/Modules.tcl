# Modules.tcl: Local include tcl script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Tomas Fukac <fukac@cesnet.cz>
#            Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SV_MVB_BASE   "$OFM_PATH/comp/mvb_tools/ver"
set SV_TCAM2_BASE "$OFM_PATH/comp/base/mem/tcam2/ver"
set SV_WB_BASE    "$SV_TCAM2_BASE/tbench/write_bus"
set SV_RB_BASE    "$SV_TCAM2_BASE/tbench/read_bus"

lappend COMPONENTS [ list "SV_MVB" $SV_MVB_BASE "FULL" ]
lappend COMPONENTS [ list "SV_WB"  $SV_WB_BASE  "FULL" ]
lappend COMPONENTS [ list "SV_RB"  $SV_RB_BASE  "FULL" ]

lappend MOD "$ENTITY_BASE/tbench/test_pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$SV_TCAM2_BASE/tbench/test.sv"
