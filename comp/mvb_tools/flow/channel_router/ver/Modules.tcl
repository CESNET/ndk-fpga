# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kriz <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause



set SV_MVB_BASE "$ENTITY_BASE/../../../ver"
set SV_MI_BASE  "$OFM_PATH/comp/mi_tools/ver"

set COMPONENTS [list \
    [ list "SV_MVB"   $SV_MVB_BASE  "FULL"] \
    [ list "SV_MI"    $SV_MI_BASE   "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/tbench/dut_wrapper.vhd"
set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
