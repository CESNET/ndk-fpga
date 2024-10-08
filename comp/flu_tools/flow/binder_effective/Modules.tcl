# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2014 CESNET
# Author: Pavel Benacek <benacek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set FLU_BASE            "$OFM_PATH/comp/flu_tools"
set BINDER_COMP_BASE    "$ENTITY_BASE/comp"

# FLU binder packages
set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"

# FLU Binder components
set ALIGN_BASE          "$BINDER_COMP_BASE/align"
set DISTRIB_BASE        "$BINDER_COMP_BASE/distrib"
set FLU2FLUA_BASE       "$BINDER_COMP_BASE/flu2flua"
set FLUA_BINDER_BASE    "$BINDER_COMP_BASE/flua_binder"
set RR_SELECT           "$BINDER_COMP_BASE/rr_select"

if { "$ARCHGRP" == "" } {
  set ARCHGRP     "FULL"
}

set COMPONENTS [list \
      [list "ALIGN"           $ALIGN_BASE          "FULL" ] \
      [list "DISTRIB"         $DISTRIB_BASE        "FULL" ] \
      [list "FLU2FLUA"        $FLU2FLUA_BASE       "FULL" ] \
      [list "FLUA_BINDER"     $FLUA_BINDER_BASE    "FULL" ] \
      [list "RR_SELECT"       $RR_SELECT           "$ARCHGRP" ] \
]

# FLU Binder
set MOD "$MOD $ENTITY_BASE/binder_sync.vhd"
set MOD "$MOD $ENTITY_BASE/binder_ent.vhd"
set MOD "$MOD $ENTITY_BASE/binder_arch.vhd"
