# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PKG_BASE             "$OFM_PATH/comp/base/pkg"
set SUM_ONE_BASE         "$OFM_PATH/comp/base/logic/sum_one"
set PIPE_TREE_ADDER_BASE "$OFM_PATH/comp/base/logic/pipe_tree_adder"
set DSP_CNT_BASE         "$OFM_PATH/comp/base/dsp/dsp_counter"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
   [list "SUM_ONE"         $SUM_ONE_BASE         "FULL" ] \
   [list "PIPE_TREE_ADDER" $PIPE_TREE_ADDER_BASE "FULL" ] \
   [list "DSP_COUNTER"     $DSP_CNT_BASE         "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/rx_stat_unit.vhd"
