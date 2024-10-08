#
# Modules.tcl: Components include script
# Copyright (C) 2012 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
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
  set MOD "$MOD $ENTITY_BASE/pipe.vhd"
  set MOD "$MOD $ENTITY_BASE/pipe_deeper.vhd"
  set MOD "$MOD $ENTITY_BASE/pipe_plus.vhd"
}

# -----------------------------------------------------------------------------
if { $ARCHGRP == "EMPTY" } {

}
