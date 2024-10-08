# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2012 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components


if { $ARCHGRP == "FULL" } {
  set SV_FLU_BASE   "$ENTITY_BASE/../../../ver"
  set SV_FL_BASE    "$OFM_PATH/comp/fl_tools/ver"

  set COMPONENTS [list \
      [ list "SV_FLU_BASE"   $SV_FLU_BASE  "FULL"] \
      [ list "SV_FL_BASE"   $SV_FL_BASE  "FULL"] \
  ]
  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
}
