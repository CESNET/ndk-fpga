# Modules.tcl: Local include tcl script
# Copyright (C) 2016 CESNET z. s. p. o.
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause



set SV_MVB_BASE   "$ENTITY_BASE/../../../ver"

set COMPONENTS [list \
    [ list "SV_MVB_BASE"   $SV_MVB_BASE  "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
