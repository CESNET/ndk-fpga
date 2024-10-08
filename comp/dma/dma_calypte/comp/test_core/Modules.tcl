# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

set MI_ASYNC_BASE              "$OFM_PATH/comp/mi_tools/async"
set MI_SPLITTER_PLUS_GEN_BASE  "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set MI_ASYNC_BASE              "$OFM_PATH/comp/mi_tools/async"
set TX_DMA_DEBUG_CORE_BASE     "$ENTITY_BASE/comp/tx_debug_core"
set MFB_LOOPBACK_BASE          "$OFM_PATH/comp/mfb_tools/flow/loopback"
set DATA_LOGGER_BASE           "$OFM_PATH/comp/debug/data_logger"
set LATENCY_METER_BASE         "$OFM_PATH/comp/debug/latency_meter"
set MFB_GENERATOR_BASE         "$OFM_PATH/comp/mfb_tools/debug/generator"

lappend COMPONENTS [ list "MI_ASYNC"             $MI_ASYNC_BASE             "FULL" ]
lappend COMPONENTS [ list "MI_SPLITTER_PLUS_GEN" $MI_SPLITTER_PLUS_GEN_BASE "FULL" ]
lappend COMPONENTS [ list "TX_DMA_DEBUG_CORE"    $TX_DMA_DEBUG_CORE_BASE    "FULL" ]
lappend COMPONENTS [ list "MFB_LOOPBACK"         $MFB_LOOPBACK_BASE         "FULL" ]
lappend COMPONENTS [ list "DATA_LOGGER"          $DATA_LOGGER_BASE          "FULL" ]
lappend COMPONENTS [ list "LATENCY_METER"        $LATENCY_METER_BASE        "FULL" ]
lappend COMPONENTS [ list "MFB_GENERATOR"        $MFB_GENERATOR_BASE        "FULL" ]

lappend MOD "$ENTITY_BASE/dma_test_core.vhd"
