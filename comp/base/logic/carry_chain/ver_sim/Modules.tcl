# Modules.tcl: Components include script
# Copyright (C) 2017 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause



set SV_VER_BASE   "$OFM_PATH/comp/ver/word_link"

set COMPONENTS [list \
      [ list "SV_VER"   $SV_VER_BASE  "FULL"] \
]
set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
