# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2009 CESNET
# Author: Ondrej Lengal <lengal@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# files with separate entity definition
set MOD "$MOD $ENTITY_BASE/squarer_ent.vhd"

if { $ARCHGRP == "FULL" } {

  # files with both entity declaration and architecture definition
  set MOD "$MOD $ENTITY_BASE/sqr_dop2_lat1.vhd"

  # files with separate architecture definition
  set MOD "$MOD $ENTITY_BASE/squarer.vhd"
}
