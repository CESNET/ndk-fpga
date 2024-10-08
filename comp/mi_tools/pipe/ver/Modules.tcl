# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2021 CESNET
# Author: Marek Santa <santa@liberouter.org>
#         Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components


if { $ARCHGRP == "FULL" } {
  set SV_BASE         "$OFM_PATH/comp/ver"
  set SV_MI32         "$OFM_PATH/comp/mi_tools/ver"
  set SV_MI_FIFO      "$OFM_PATH/comp/mi_tools/ver_fifo"

  set COMPONENTS [list \
      [ list "SV_BASE"    $SV_BASE    "FULL"    ] \
      [ list "SV_MI32"    $SV_MI32    "UNIFIED" ] \
      [ list "SV_MIFIFO"  $SV_MI_FIFO "FIFO"    ] \
  ]

  set MOD "$MOD $SV_MI_FIFO/sv_mi_common_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
}
