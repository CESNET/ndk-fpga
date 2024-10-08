# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
#            Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components


if { $ARCHGRP == "FULL" } {
  set SV_FL_BASE   "$ENTITY_BASE/.."

  set COMPONENTS [list \
      [ list "SV_FL_BASE"   $SV_FL_BASE  "FULL"] \
  ]
  set MOD "$MOD $ENTITY_BASE/ethernet_type_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/ip_protocol_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/packet_generator_pkg.sv"
}
