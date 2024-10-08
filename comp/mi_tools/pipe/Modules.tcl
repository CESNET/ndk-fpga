# Modules.tcl: Local include tcl script
# Copyright (C) 2010 CESNET
# Author(s): Vaclav Bartos <washek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# -----------------------------------------------------------------------------

if { $ARCHGRP == "FULL" } {

  set COMPONENTS [list \
      [list "PIPE"  "$OFM_PATH/comp/base/misc/pipe"   "FULL"] \
  ]

  set MOD "$MOD $ENTITY_BASE/mi_pipe.vhd"
  set MOD "$MOD $ENTITY_BASE/mi_pipe_arch.vhd"
}

# -----------------------------------------------------------------------------

if { $ARCHGRP == "EMPTY" } {

}
