#
# Modules.tcl: Components include script
# Copyright (C) 2008 CESNET
# Author: Martin Kosek <kosek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# -----------------------------------------------------------------------------

if { $ARCHGRP == "FULL" } {

  set PIPE_BASE   "$OFM_PATH/comp/base/misc/pipe"

  set COMPONENTS [list \
      [list "PIPE"    $PIPE_BASE     "FULL"] \
  ]

  # packages
  set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
  set PACKAGES "$PACKAGES $OFM_PATH/comp/fl_tools/pkg/fl_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/pipe.vhd"
  set MOD "$MOD $ENTITY_BASE/top/pipe_fl16.vhd"
  set MOD "$MOD $ENTITY_BASE/top/pipe_fl32.vhd"
  set MOD "$MOD $ENTITY_BASE/top/pipe_fl64.vhd"
}

# -----------------------------------------------------------------------------
if { $ARCHGRP == "EMPTY" } {

}
