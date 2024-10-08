# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2014 CESNET
# Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#

set MATH_PKG     "$OFM_PATH/comp/base/pkg"
set PIPE_BASE   "$OFM_PATH/comp/base/misc/pipe"
set FLU_PIPE_BASE       "$OFM_PATH/comp/flu_tools/flow/pipe"
set QDR_BASE     "$ENTITY_BASE/comp/qdr"
set FLU2QDR_BASE "$ENTITY_BASE/comp/flu2qdr"
set FLU_ADAPTER_PKG      "$ENTITY_BASE/pkg/"

set PACKAGES   "$PACKAGES  $MATH_PKG/math_pack.vhd"
set PACKAGES   "$PACKAGES  $FLU_ADAPTER_PKG/flu_adapter_pkg.vhd"

set MOD "$MOD $ENTITY_BASE/flu_adapter_ent.vhd"
set MOD "$MOD $ENTITY_BASE/flu_adapter_arch.vhd"

# Components
set COMPONENTS [list \
      [list "PIPE"    $PIPE_BASE     "FULL"] \
      [ list "FLU_PIPE"             $FLU_PIPE_BASE          "FULL" ] \
      [ list "QDR"             $QDR_BASE          "FULL" ] \
      [ list "FLU2QDR"             $FLU2QDR_BASE          "FULL" ] \
]
