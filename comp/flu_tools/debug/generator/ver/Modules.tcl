# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2018 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set COMPONENTS [list \
    [ list "SV_FLU_BASE"   "$ENTITY_BASE/../../../ver"  "FULL"] \
    [ list "SV_MI_BASE"    "$OFM_PATH/comp/mi_tools/ver/sw_access"  "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
