# Modules.tcl: Local include tcl script
# Copyright (C) 2020 CESNET
# Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>

# SPDX-License-Identifier: BSD-3-Clause
set SV_MFB_BASE   "$ENTITY_BASE/../../../ver"

set COMPONENTS [list \
      [ list "SV_MFB"   $SV_MFB_BASE  "FULL"] \
]
set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"

