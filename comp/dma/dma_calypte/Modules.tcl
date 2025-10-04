# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#


lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGEG "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGEG "$OFM_PATH/comp/base/pkg/pcie_meta_pack.vhd"

set RX_CALYPTE_BASE           "$ENTITY_BASE/comp/rx"
set TX_CALYPTE_BASE           "$ENTITY_BASE/comp/tx"
set PTR_UPDATER_BASE          "$ENTITY_BASE/comp/ptr_updater"
set MFB_MERGER_BASE           "$OFM_PATH/comp/mfb_tools/flow/merger_simple"
set MI_SPLITTER_PLUS_GEN_BASE "$OFM_PATH/comp/mi_tools/splitter_plus_gen"

lappend COMPONENTS [ list "RX_DMA_CALYPTE"       $RX_CALYPTE_BASE           "FULL"]
lappend COMPONENTS [ list "TX_DMA_CALYPTE"       $TX_CALYPTE_BASE           "FULL"]
lappend COMPONENTS [ list "DMA_PTR_UPDATER"      $PTR_UPDATER_BASE          "FULL"]
lappend COMPONENTS [ list "MFB_MERGER_SIMPLE"    $MFB_MERGER_BASE           "FULL"]
lappend COMPONENTS [ list "MI_SPLITTER_PLUS_GEN" $MI_SPLITTER_PLUS_GEN_BASE "FULL"]

lappend MOD "$ENTITY_BASE/dma_calypte.vhd"
lappend MOD "$ENTITY_BASE/DevTree.tcl"
