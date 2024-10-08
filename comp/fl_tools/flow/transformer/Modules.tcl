# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2006 CESNET
# Author: Martin Louda <sandin@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE    "$OFM_PATH/comp/base/pkg"
set MUX_BASE    "$OFM_PATH/comp/base/logic/mux"
set FL_BASE     "$OFM_PATH/comp/fl_tools"

# Source files for all architectures
set MOD "$MOD $FL_BASE/pkg/fl_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/transformer_ent.vhd"

# Full architecture of FrameLink Transformer
if { $ARCHGRP == "FULL" } {
    set MOD "$MOD $ENTITY_BASE/transformer_down.vhd"
    set MOD "$MOD $ENTITY_BASE/transformer_up.vhd"
    set MOD "$MOD $ENTITY_BASE/transformer_down_8.vhd"
    set MOD "$MOD $ENTITY_BASE/transformer_up_8.vhd"
    set MOD "$MOD $ENTITY_BASE/transformer.vhd"
}

# Empty architecture of FrameLink Transformer
if { $ARCHGRP == "EMPTY" } {
    set MOD "$MOD $ENTITY_BASE/transformer_empty.vhd"
}


# components
set COMPONENTS [list \
    [list "PKG_MATH"        $PKG_BASE       "MATH"]     \
    [list "GEN_MUX"         $MUX_BASE       "FULL"]     \
]

# covers
set MOD "$MOD $ENTITY_BASE/top/transformer_fl128_16.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl128_32.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl128_64.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl64_16.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl64_128.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl16_32.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl16_64.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl32_16.vhd"
