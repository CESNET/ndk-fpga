# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE     "$OFM_PATH/comp/base/pkg"
set SUBCOMP_BASE "$ENTITY_BASE/comp"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set FIFOX_BASE       "$OFM_PATH/comp/base/fifo/fifox"
set ASFIFOX_BASE     "$OFM_PATH/comp/base/fifo/asfifox"

set COMPONENTS [list \
    [ list "TRANS_SORTER"     "$OFM_PATH/comp/base/misc/trans_sorter"   "FULL" ] \
    [ list "TRANS_COLOR_GEN"  "$SUBCOMP_BASE/trans_color_gen"       "FULL" ] \
    [ list "TRANS_BREAKER"    "$SUBCOMP_BASE/trans_breaker"         "FULL" ] \
    [ list "UINSTR_GEN"       "$SUBCOMP_BASE/uinstr_gen"            "FULL" ] \
    [ list "UINSTR_SPLIT"     "$SUBCOMP_BASE/uinstr_splitter"       "FULL" ] \
    [ list "PLANNER"          "$SUBCOMP_BASE/planner"               "FULL" ] \
    [ list "PLANNER_SYNCH"    "$SUBCOMP_BASE/planner_synch"         "FULL" ] \
    [ list "CROSSBAR"         "$SUBCOMP_BASE/crossbar"              "FULL" ] \
    [ list "FIFOX"            "$FIFOX_BASE"                         "FULL" ] \
    [ list "ASFIFOX"          "$ASFIFOX_BASE"                       "FULL" ] \
    [ list "SHAKEDOWN"        "$OFM_PATH/comp/mvb_tools/flow/shakedown" "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/crossbarx.vhd"
#set MOD "$MOD $ENTITY_BASE/crossbarx_stream.vhd"
