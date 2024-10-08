# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE     "$OFM_PATH/comp/base/pkg"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set MUX_ONEHOT_BASE "$OFM_PATH/comp/base/logic/mux"
set BIN2HOT_BASE    "$OFM_PATH/comp/base/logic/bin2hot"
set FIRST_ONE_BASE  "$OFM_PATH/comp/base/logic/first_one"
set GEN_ENC_BASE    "$OFM_PATH/comp/base/logic/enc"
set GEN_NOR_BASE    "$OFM_PATH/comp/base/logic/gen_nor"
set GEN_AND_BASE    "$OFM_PATH/comp/base/logic/and"
set PIPE_BASE       "$OFM_PATH/comp/base/misc/pipe"

set COMPONENTS [list \
    [ list "GEN_MUX_ONEHOT" $MUX_ONEHOT_BASE  "FULL"       ] \
    [ list "BIN2HOT"        $BIN2HOT_BASE     "FULL"       ] \
    [ list "FIRST_ONE"      $FIRST_ONE_BASE   "FULL"       ] \
    [ list "GEN_ENC"        $GEN_ENC_BASE     "behavioral" ] \
    [ list "GEN_NOR"        $GEN_NOR_BASE     "behav"      ] \
    [ list "GEN_AND"        $GEN_AND_BASE     "behav"      ] \
    [ list "PIPE"           $PIPE_BASE        "FULL"       ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/planner.vhd"
