# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components


if { $ARCHGRP == "FULL" } {
  set SV_COMMON_BASE   "$OFM_PATH/comp/ver"

  set COMPONENTS [list \
      [ list "SV_COMMON"   $SV_COMMON_BASE    "FULL"] \
   ]

  set MOD "$MOD $ENTITY_BASE/sv_pcd_pkg.sv"
}
