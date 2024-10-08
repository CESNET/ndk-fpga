# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2014 CESNET
# Author: Pavel Benacek <benacek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set FLU_BASE            "$OFM_PATH/comp/flu_tools"
set BINDER_COMP_BASE    "$ENTITY_BASE/.."

# FLU binder packages
set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"

# FLU Binder components
set ALIGN_BASE          "$BINDER_COMP_BASE/align"
set DISTRIB_BASE        "$BINDER_COMP_BASE/distrib"
set FLU_FIFO_BASE       "$FLU_BASE/storage/fifo"
set FIFO_BASE           "$OFM_PATH/comp/base/fifo/fifo"

set COMPONENTS [list \
      [list "ALIGN"     $ALIGN_BASE    ] \
      [list "DISTRIB"   $DISTRIB_BASE  ] \
      [list "FLU_FIFO"  $FLU_FIFO_BASE    "FULL"   ] \
      [list "FIFO"      $FIFO_BASE        "BEHAV"  ] \
]


# FLU to FLUA converter
set MOD "$MOD $ENTITY_BASE/flu2flua_ent.vhd"
set MOD "$MOD $ENTITY_BASE/flu2flua_arch_core.vhd"
set MOD "$MOD $ENTITY_BASE/flu2flua_arch.vhd"
