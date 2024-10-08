#
# Modules.tcl: Local include tcl script
# Copyright (C) 2008 CESNET
# Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# -----------------------------------------------------------------------------

if { $ARCHGRP == "FULL" } {

  set MEMORY_BASE "$OFM_PATH/comp/base/mem/sp_bmem"
  set MEMORY_BASE2 "$OFM_PATH/comp/base/mem/gen_lutram/compatibility"

  set COMPONENTS [list \
      [list "MEMORY"    $MEMORY_BASE     "FULL"] \
      [list "MEMORY2"   $MEMORY_BASE2    "FULL"] \
  ]

  set MOD "$MOD $ENTITY_BASE/testbench.vhd"

}

# -----------------------------------------------------------------------------

if { $ARCHGRP == "EMPTY" } {

}
