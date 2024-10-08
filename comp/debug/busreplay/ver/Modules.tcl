# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2016 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SWTOOLS_BASE     "$OFM_PATH/comp/mi_tools/ver/sw_access/nfb/tools"
set SV_FLU_BASE   "$OFM_PATH/comp/flu_tools/ver"

set SV_LIB "$SV_LIB $SWTOOLS_BASE/busdump/busdump"
set SV_LIB "$SV_LIB $SWTOOLS_BASE/busreplay/busreplay"

set COMPONENTS [list \
    [ list "SV_FLU_BASE"   $SV_FLU_BASE  "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
