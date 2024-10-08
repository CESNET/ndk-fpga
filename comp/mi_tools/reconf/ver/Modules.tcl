# Modules.tcl
# Copyright (C) 2021 CESNET
# Author(s): Jan Kubalek <kubalek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

if { $ARCHGRP == "FULL" } {
  set SV_BASE         "$OFM_PATH/comp/ver"
  set SV_MI32         "$OFM_PATH/comp/mi_tools/ver"

  set COMPONENTS [list \
      [ list "SV_BASE"    $SV_BASE    "FULL"    ] \
      [ list "SV_MI32"    $SV_MI32    "UNIFIED" ] \
  ]

  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/cov.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
}
