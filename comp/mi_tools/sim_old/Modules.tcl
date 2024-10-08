# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

global VHDL_BASE

if { $ARCHGRP == "FULL" } {
  set LB_ENDPOINT_BASE   "$ENTITY_BASE/comp/lb_endpoint"
  set LB_ROOT_BASE       "$ENTITY_BASE/comp/lb_root"
  set IB_SIM_BASE        "$ENTITY_BASE/comp/ib_sim"

  set PACKAGES "$PACKAGES $ENTITY_BASE/../pkg/mi32_pkg.vhd"

  set COMPONENTS [list \
      [list "LB_ENDPOINT"  $LB_ENDPOINT_BASE       "FULL"] \
      [list "LB_ROOT"      $LB_ROOT_BASE           "FULL"] \
      [list "IB_SIM"       $IB_SIM_BASE            "FULL"] \
  ]

  set MOD "$MOD $ENTITY_BASE/mi32_sim.vhd"
}
