#
# Modules.tcl: Local include tcl script
# Copyright (C) 2008 CESNET
# Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# -----------------------------------------------------------------------------


  set MI_SIM_BASE "$ENTITY_BASE/.."
  set MEMORY_BASE "$OFM_PATH/comp/base/mem/sp_distmem"

  set COMPONENTS [list \
      [list "MEMORY"    $MEMORY_BASE     "FULL"] \
      [list "MI_SIM"    $MI_SIM_BASE     "FULL"] \
  ]

  set MOD "$MOD $ENTITY_BASE/testbench.vhd"

