# Copyright (C) 2019 CESNET
# Author(s): Lukas Hejcman <xhejcm01@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set SV_VER_BASE  "$OFM_PATH/comp/ver"
set SV_MI32_BASE "$OFM_PATH/comp/mi_tools/ver"

set COMPONENTS [list \
      [ list "SV_VER"  $SV_VER_BASE  "FULL"] \
      [ list "SV_MI32" $SV_MI32_BASE "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
