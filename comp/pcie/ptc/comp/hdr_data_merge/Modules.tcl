# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set GEN_MUX_BASE       "$OFM_PATH/comp/base/logic/mux"
set SUM_ONE_BASE       "$OFM_PATH/comp/base/logic/sum_one"
set DEC_BASE           "$OFM_PATH/comp/base/logic/dec1fn"
set FIFOX_MULTI_BASE   "$OFM_PATH/comp/base/fifo/fifox_multi"
set MVB_SHAKEDOWN_BASE "$OFM_PATH/comp/mvb_tools/flow/shakedown"

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/dma_bus_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
   [list "GEN_MUX"        $GEN_MUX_BASE       "FULL" ] \
   [list "SUM_ONE"        $SUM_ONE_BASE       "FULL" ] \
   [list "DEC1FN2B"       $DEC_BASE           "FULL" ] \
   [list "FIFOX_MULTI"    $FIFOX_MULTI_BASE   "FULL" ] \
   [list "MVB_SHAKEDOWN"  $MVB_SHAKEDOWN_BASE "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/ptc_hdr_data_merge_hpai.vhd"
set MOD "$MOD $ENTITY_BASE/ptc_hdr_data_merge_dins.vhd"
set MOD "$MOD $ENTITY_BASE/ptc_hdr_data_merge.vhd"
