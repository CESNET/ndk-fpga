# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Vladislav Valek
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set ASYNC_RESET_BASE            "$OFM_PATH/comp/base/async/reset"
set MI_SPLITTER_PLUS_BASE       "$OFM_PATH/comp/mi_tools/splitter_plus"
set MI_SPLITTER_PLUS_GEN_BASE   "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set MI_ASYNC_BASE               "$OFM_PATH/comp/mi_tools/async"
set MFB_ASFIFOX_BASE            "$OFM_PATH/comp/mfb_tools/storage/asfifox"
set MFB_META_INS_BASE           "$OFM_PATH/comp/mfb_tools/flow/metadata_insertor"
set MFB_META_EXT_BASE           "$OFM_PATH/comp/mfb_tools/flow/metadata_extractor"
set MFB_RECONFIG_BASE           "$OFM_PATH/comp/mfb_tools/flow/reconfigurator"
set TSU_BASE                    "$OFM_PATH/comp/tsu/tsu_gen"
set MFB_PIPE_BASE               "$OFM_PATH/comp/mfb_tools/flow/pipe"

set DMA_MEDUSA_BASE             "$ENTITY_BASE/../../../../../../modules/ndk-mod-dma-medusa"
set DMA_CALYPTE_BASE            "$OFM_PATH/comp/dma/dma_calypte"
set DMA_TEST_CORE_BASE          "$OFM_PATH/comp/dma/dma_calypte/comp/test_core"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/dma_bus_pack.vhd"

lappend MOD "$ENTITY_BASE/dma_wrapper_ent.vhd"

lappend COMPONENTS [ list "MI_ASYNC" $MI_ASYNC_BASE "FULL" ]

if { $ARCHGRP == "MEDUSA" } {

    lappend COMPONENTS [ list "MI_SPLITTER_PLUS_GEN" $MI_SPLITTER_PLUS_GEN_BASE "FULL" ]
    lappend COMPONENTS [ list "ASYNC_RESET"          $ASYNC_RESET_BASE          "FULL" ]
    lappend COMPONENTS [ list "DMA_MEDUSA"           $DMA_MEDUSA_BASE           "FULL" ]

    # Source files for implemented component
    lappend MOD "$ENTITY_BASE/dma_medusa_wrapper_arch.vhd"

} elseif { $ARCHGRP == "CALYPTE" } {

    lappend COMPONENTS [ list "MI_SPLITTER_PLUS_GEN"   $MI_SPLITTER_PLUS_GEN_BASE  "FULL" ]
    lappend COMPONENTS [ list "MFB_ASFIFOX"            $MFB_ASFIFOX_BASE           "FULL" ]
    lappend COMPONENTS [ list "METADATA_INSERTOR"      $MFB_META_INS_BASE          "FULL" ]
    lappend COMPONENTS [ list "METADATA_EXTRACTOR"     $MFB_META_EXT_BASE          "FULL" ]
    lappend COMPONENTS [ list "TSU_GEN"                $TSU_BASE                   "FULL" ]
    lappend COMPONENTS [ list "MFB_PIPE"               $MFB_PIPE_BASE              "FULL" ]
    lappend COMPONENTS [ list "DMA_CALYPTE"            $DMA_CALYPTE_BASE           "FULL" ]
    lappend COMPONENTS [ list "MFB_RECONFIG"           $MFB_RECONFIG_BASE          "FULL" ]
    lappend COMPONENTS [ list "DMA_TEST_CORE"          $DMA_TEST_CORE_BASE         "FULL" ]

    lappend MOD "$ENTITY_BASE/dma_calypte_wrapper_arch.vhd"
}
