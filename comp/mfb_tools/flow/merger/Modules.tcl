# Modules.tcl: Script to compile single module
# Copyright (C) 2023 CESNET
# Author: Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set FIFOXM_BASE       "$OFM_PATH/comp/base/fifo/fifox_multi"
set AUX_BASE          "$OFM_PATH/comp/mfb_tools/logic/auxiliary_signals"
set MVB_PIPE_BASE     "$OFM_PATH/comp/mvb_tools/flow/pipe"
set MFB_PIPE_BASE     "$OFM_PATH/comp/mfb_tools/flow/pipe"
set PIPE_REG_BASE     "$OFM_PATH/comp/base/misc/pipe"
set SHAKEDOWN_BASE    "$OFM_PATH/comp/mvb_tools/flow/shakedown"
set MVB_MERGE_ST_BASE "$OFM_PATH/comp/mvb_tools/flow/merge_streams"

set PKG_BASE "$OFM_PATH/comp/base/pkg"

lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"
lappend PACKAGES "$PKG_BASE/dma_bus_pack.vhd"

# list of sub-components
lappend COMPONENTS [ list "FIFOX_MULTI"  $FIFOXM_BASE      "FULL" ]
lappend COMPONENTS [ list "AUX"          $AUX_BASE         "FULL" ]
lappend COMPONENTS [ list "MVB_PIPE"     $MVB_PIPE_BASE    "FULL" ]
lappend COMPONENTS [ list "MFB_PIPE"     $MFB_PIPE_BASE    "FULL" ]
lappend COMPONENTS [ list "PIPE_REG"     $PIPE_REG_BASE    "FULL" ]
lappend COMPONENTS [ list "SHAKEDOWN"    $SHAKEDOWN_BASE   "FULL" ]
lappend COMPONENTS [ list "MVB_MERGE_ST" $MVB_MERGE_ST_BASE "FULL" ]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mfb_merger_ent.vhd"
set MOD "$MOD $ENTITY_BASE/mfb_merger_old.vhd"
#######
# !!! MUST BE INCLUDED LAST TO BECOME THE DEFAULT ARCHITECTURE !!!
set MOD "$MOD $ENTITY_BASE/mfb_merger_full.vhd"
#######
set MOD "$MOD $ENTITY_BASE/mfb_merger_gen.vhd"
