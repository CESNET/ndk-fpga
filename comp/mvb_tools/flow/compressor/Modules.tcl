# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set MERGE_N_TO_M_BASE   "$OFM_PATH/comp/mvb_tools/flow/merge_n_to_m"
set SUM_ONE_BASE        "$OFM_PATH/comp/base/logic/sum_one"

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
   [list "MERGE_N_TO_M"       $MERGE_N_TO_M_BASE   "FULL" ] \
   [list "SUM_ONE"            $SUM_ONE_BASE        "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mvb_compressor.vhd"
