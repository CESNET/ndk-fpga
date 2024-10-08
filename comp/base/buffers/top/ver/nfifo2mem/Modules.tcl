# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2008 CESNET
# Author: Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

if { $ARCHGRP == "FULL" } {
  set SV_FIFO_BASE     "$ENTITY_BASE/../../../ver"
  #set SV_COMMON_BASE   "$OFM_PATH/comp/ver"


  set COMPONENTS [list \
      [ list "SV_FIFO_BASE"   $SV_FIFO_BASE  "FULL"] \
   ]
  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
}
