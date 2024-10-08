# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2014 CESNET
# Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#

set FLU_ADAPTER_BASE "$OFM_PATH/comp/flu_tools/qdr/flu_adapter/"
set MUX_BASE  "$OFM_PATH/comp/base/logic/mux"
set MATH_PKG     "$OFM_PATH/comp/base/pkg"
set FLU_ADAPTER_PKG "$FLU_ADAPTER_BASE/pkg"
set FLU_PIPE_BASE       "$OFM_PATH/comp/flu_tools/flow/pipe"

set PACKAGES   "$PACKAGES  $MATH_PKG/math_pack.vhd"
set PACKAGES   "$PACKAGES  $FLU_ADAPTER_PKG/flu_adapter_pkg.vhd"

set MOD "$MOD $ENTITY_BASE/flu2qdr_ent.vhd"
set MOD "$MOD $ENTITY_BASE/flu2qdr_arch.vhd"

# Components
set COMPONENTS [list \
      [list "MUX"     $MUX_BASE   "FULL"] \
      [ list "FLU_PIPE"             $FLU_PIPE_BASE          "FULL" ] \
]
