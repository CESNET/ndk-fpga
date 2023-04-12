# Modules.tcl: script to compile single module
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# converting input list to associative array (uncomment when needed)
array set ARCHGRP_ARR $ARCHGRP

# Component paths
set MI_ASYNC_BASE       "$OFM_PATH/comp/mi_tools/async"
set MI_SPLITTER_BASE    "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set MFB_PIPE_BASE       "$OFM_PATH/comp/mfb_tools/flow/pipe"
set MFB_META_INS_BASE   "$OFM_PATH/comp/mfb_tools/flow/metadata_insertor"
set MVB_PIPE_BASE       "$OFM_PATH/comp/mvb_tools/flow/pipe"
set MVB_CHDIST_BASE     "$OFM_PATH/comp/mvb_tools/flow/channel_router"
set APP_CORE_UTILS_BASE "$OFM_PATH/../core/intel/src/comp/app_core_utils"
set STREAMS_MERGER_BASE "$APP_CORE_UTILS_BASE/dma_streams_merger"
set DMA_CHAN_MOD_BASE   "$APP_CORE_UTILS_BASE/dma_chan_mod"
set MEM_TESTER_BASE     "$OFM_PATH/comp/debug/mem_tester"
set MEM_LOGGER_BASE     "$OFM_PATH/comp/debug/data_logger/mem_logger"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/eth_hdr_pack.vhd"

if {$ARCHGRP_ARR(APP_CORE_ENABLE)} {
    # Components
    lappend COMPONENTS [ list "MI_ASYNC"       $MI_ASYNC_BASE       "FULL" ]
    lappend COMPONENTS [ list "MI_SPLITTER"    $MI_SPLITTER_BASE    "FULL" ]
    lappend COMPONENTS [ list "MFB_META_INS"   $MFB_META_INS_BASE   "FULL" ]
    lappend COMPONENTS [ list "MFB_PIPE"       $MFB_PIPE_BASE       "FULL" ]
    lappend COMPONENTS [ list "MVB_PIPE"       $MVB_PIPE_BASE       "FULL" ]
    lappend COMPONENTS [ list "STREAMS_MERGER" $STREAMS_MERGER_BASE "FULL" ]
    lappend COMPONENTS [ list "DMA_CHAN_MOD"   $DMA_CHAN_MOD_BASE   "FULL" ]
    lappend COMPONENTS [ list "MVB_CHDIST"     $MVB_CHDIST_BASE     "FULL" ]
    lappend COMPONENTS [ list "MEM_TESTER"     $MEM_TESTER_BASE     "FULL" ]
    lappend COMPONENTS [ list "MEM_LOGGER"     $MEM_LOGGER_BASE     "FULL" ]

    # Files
    lappend MOD "$ENTITY_BASE/app_subcore.vhd"
    lappend MOD "$ENTITY_BASE/application_core.vhd"
} else {
    lappend MOD "$APP_CORE_UTILS_BASE/app_core_empty_arch.vhd"
}

lappend MOD "$ENTITY_BASE/DevTree.tcl"
