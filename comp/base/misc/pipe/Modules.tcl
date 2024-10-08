#
# Modules.tcl: Components include script
# Copyright (C) 2013 CESNET
# Author: Tomas Malek <tomalek@liberouter.org>
#         Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# -----------------------------------------------------------------------------

if { $ARCHGRP == "FULL" } {

  set SH_REG_BASE_BASE  "$OFM_PATH/comp/base/shreg/sh_reg_base"
  set DEBUG_PROBE_BASE  "$OFM_PATH/comp/debug/streaming_debug"

  set COMPONENTS [list \
      [list "SH_REG_BASE_DYNAMIC"    $SH_REG_BASE_BASE     "FULL"]  \
      [list "DEBUG_PROBE"           $DEBUG_PROBE_BASE     "PROBE"] \
  ]

  # packages
  set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
  # modules
  set MOD "$MOD $ENTITY_BASE/pipe_reg.vhd"
  set MOD "$MOD $ENTITY_BASE/pipe.vhd"
  set MOD "$MOD $ENTITY_BASE/pipe_arch.vhd"
  set MOD "$MOD $ENTITY_BASE/pipe_deeper.vhd"
  set MOD "$MOD $ENTITY_BASE/pipe_deeper_arch.vhd"
}

# -----------------------------------------------------------------------------

if { $ARCHGRP == "EMPTY" } {

}
