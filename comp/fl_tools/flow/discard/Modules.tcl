# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2010 CESNET
# Author: Viktor Pus <pus@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE    "$OFM_PATH/comp/base/pkg"
set MUX_BASE    "$OFM_PATH/comp/base/logic/mux"
set DEC1FN_BASE "$OFM_PATH/comp/base/logic/dec1fn"
set DP_DISTMEM_BASE "$OFM_PATH/comp/base/mem/gen_lutram/compatibility"
set FL_BASE     "$OFM_PATH/comp/fl_tools"

# Source files for all architectures
set MOD "$MOD $ENTITY_BASE/discard_ent.vhd"
set MOD "$MOD $ENTITY_BASE/discard_stat_ent.vhd"

# Full architecture of FrameLink Transformer
if { $ARCHGRP == "FULL" } {
    set MOD "$MOD $ENTITY_BASE/discard_arch.vhd"
    set MOD "$MOD $ENTITY_BASE/discard_stat_arch.vhd"
}


# components
set COMPONENTS [list \
    [list "PKG_MATH"        $PKG_BASE         "MATH"]    \
    [list "GEN_MUX"         $MUX_BASE         "FULL"]    \
    [list "DP_DISTMEM"      $DP_DISTMEM_BASE  "FULL"]    \
    [list "DEC1FN_ENABLE"   $DEC1FN_BASE      "FULL"]    \
]
