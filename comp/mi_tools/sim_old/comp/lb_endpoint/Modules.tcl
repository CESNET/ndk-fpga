# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

if { $ARCHGRP == "FULL" } {
   set COMPONENTS [list \
     [list "PKG"          "$OFM_PATH/comp/base/pkg"            "MATH"]  \
  ]

  set MOD "$MOD $ENTITY_BASE/../lb_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/../../../pkg/mi32_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/lb_endpoint_buffer.vhd"
  set MOD "$MOD $ENTITY_BASE/lb_endpoint_50mhz.vhd"
  set MOD "$MOD $ENTITY_BASE/lb_endpoint_100mhz.vhd"
  set MOD "$MOD $ENTITY_BASE/lb_endpoint.vhd"
  set MOD "$MOD $ENTITY_BASE/lb_endpoint_arch.vhd"
  set MOD "$MOD $ENTITY_BASE/lb_endpoint_norec.vhd"

  }
