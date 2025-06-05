# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

set MI_ASYNC_BASE              "$OFM_PATH/comp/mi_tools/async"
set DATA_LOGGER_BASE           "$OFM_PATH/comp/debug/data_logger"
set LATENCY_METER_BASE         "$OFM_PATH/comp/debug/latency_meter"
set MFB_GENERATOR_BASE         "$OFM_PATH/comp/mfb_tools/debug/generator"
set MFB_META_EXT_BASE          "$OFM_PATH/comp/mfb_tools/flow/metadata_extractor"

lappend COMPONENTS [ list "MI_ASYNC"             $MI_ASYNC_BASE             "FULL" ]
lappend COMPONENTS [ list "DATA_LOGGER"          $DATA_LOGGER_BASE          "FULL" ]
lappend COMPONENTS [ list "LATENCY_METER"        $LATENCY_METER_BASE        "FULL" ]
lappend COMPONENTS [ list "MFB_GENERATOR"        $MFB_GENERATOR_BASE        "FULL" ]
lappend COMPONENTS [ list "METADATA_EXTRACTOR"   $MFB_META_EXT_BASE         "FULL" ]

lappend MOD "$ENTITY_BASE/dma_latency_meter.vhd"
lappend MOD "$ENTITY_BASE/DevTree.tcl"
