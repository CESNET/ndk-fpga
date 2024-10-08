# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set PKG_BASE         "$OFM_PATH/comp/base/pkg"
set FIRST_ONE_BASE   "$OFM_PATH/comp/base/logic/first_one"
set ENC_BASE         "$OFM_PATH/comp/base/logic/enc"
set MUX_BASE         "$OFM_PATH/comp/base/logic/mux"
set DEMUX_BASE       "$OFM_PATH/comp/base/logic/demux"
set SUM_ONE_BASE     "$OFM_PATH/comp/base/logic/sum_one"
set SHAKEDOWN_BASE   "$OFM_PATH/comp/mvb_tools/flow/merge_n_to_m"
set SPLIT_BASE       "$OFM_PATH/comp/mvb_tools/flow/split"
set BARREL_SH_BASE   "$OFM_PATH/comp/base/logic/barrel_shifter"
set PIPE_BASE        "$OFM_PATH/comp/mvb_tools/flow/pipe"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
   [ list "SHAKEDOWN" $SHAKEDOWN_BASE  "FULL" ] \
   [ list "FIRST_ONE" $FIRST_ONE_BASE  "FULL" ] \
   [ list "ENC"       $ENC_BASE        "FULL" ] \
   [ list "MUX"       $MUX_BASE        "FULL" ] \
   [ list "SUM_ONE"   $SUM_ONE_BASE    "FULL" ] \
   [ list "DEMUX"     $DEMUX_BASE      "FULL" ] \
   [ list "BARREL_SH" $BARREL_SH_BASE  "FULL" ] \
   [ list "MVB_SPLIT" $SPLIT_BASE      "FULL" ] \
   [ list "MVB_PIPE"  $PIPE_BASE       "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mvb_shakedown.vhd"
