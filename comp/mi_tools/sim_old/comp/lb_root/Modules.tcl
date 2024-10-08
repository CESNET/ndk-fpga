# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components


if { $ARCHGRP == "FULL" } {
  set IB_ENDPOINT_BASE   "$ENTITY_BASE/../ib_endpoint"

  set COMPONENTS [list \
      [list "IB_ENDPOINT"  $IB_ENDPOINT_BASE          "FULL"] \
      [list "FIFO"         $OFM_PATH/comp/base/fifo/fifo  "FULL"] \
      [list "FIFO_BRAM"    $OFM_PATH/comp/base/fifo/fifo_bram "FULL"] \
  ]

  set MOD "$MOD $ENTITY_BASE/../lb_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/lb_root_core_fsm.vhd"
  set MOD "$MOD $ENTITY_BASE/lb_root_core.vhd"
  set MOD "$MOD $ENTITY_BASE/lb_root_buffer.vhd"
  set MOD "$MOD $ENTITY_BASE/lb_root.vhd"
  set MOD "$MOD $ENTITY_BASE/lb_root_arch.vhd"
  set MOD "$MOD $ENTITY_BASE/lb_root_norec.vhd"
}
