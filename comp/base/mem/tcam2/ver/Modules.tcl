# Modules.tcl: Local include tcl script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# set paths

set SV_MVB_BASE   "$OFM_PATH/comp/mvb_tools/ver"
set SV_WB_BASE    "$ENTITY_BASE/tbench/write_bus"

set COMPONENTS [list \
    [ list "SV_MVB"   $SV_MVB_BASE  "FULL"] \
    [ list "SV_WB"    $SV_WB_BASE   "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
