#
# Modules.tcl: Local include tcl script
# Copyright (C) 2009 CESNET
# Author(s): Vaclav Bartos <washek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# -----------------------------------------------------------------------------

set PKG_BASE         "$OFM_PATH/comp/base/pkg"
set MUX_BASE         "$OFM_PATH/comp/base/logic/mux"

if { $ARCHGRP == "FULL" } {

   set COMPONENTS [list \
      [list "GENMUX"      $MUX_BASE   "FULL"]   \
      [list "PKG_MATH"    $PKG_BASE   "MATH"]   \
      [list "PKG_TYPE"    $PKG_BASE   "TYPE"]   \
   ]

   set MOD "$MOD $ENTITY_BASE/barrel_shifter_gen.vhd"
   set MOD "$MOD $ENTITY_BASE/barrel_shifter.vhd"
   set MOD "$MOD $ENTITY_BASE/barrel_shifter_gen_piped.vhd"

}

# -----------------------------------------------------------------------------

if { $ARCHGRP == "EMPTY" } {

}
