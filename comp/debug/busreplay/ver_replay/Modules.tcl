# Modules.tcl: Modules.tcl script to compile the design
# Copyright (C) 2018 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SWTOOLS_BASE     "$OFM_PATH/comp/mi_tools/ver/sw_access/nfb/tools"

set SV_LIB "$SV_LIB $SWTOOLS_BASE/busreplay/busreplay"

set COMPONENTS [list \
    [ list "SV_MI32"    "$OFM_PATH/comp/mi_tools/ver" "FULL"] \
    [ list "BUSREPLAY"  "$OFM_PATH/comp/debug/busreplay"   "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/top_ver.vhd"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
