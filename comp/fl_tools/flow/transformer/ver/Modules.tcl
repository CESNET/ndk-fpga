# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components


# Choose native SV scoreboard
if { $ARCHGRP == "FULL" } {
  set SV_FL_BASE   "$ENTITY_BASE/../../../ver"
#  set DPI_BASE     "$ENTITY_BASE/tbench/dpi"

  set COMPONENTS [list \
      [ list "SV_FL_BASE"   $SV_FL_BASE  "FULL"] \
   ]

#  set SV_LIB "$SV_LIB $ENTITY_BASE/tbench/dpi/dpi_scoreboard_pkg"

  set MOD "$MOD $ENTITY_BASE/tbench/dpi/dpi_scoreboard_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
}
