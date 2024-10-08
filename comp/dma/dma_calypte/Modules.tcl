# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#


lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGEG "$OFM_PATH/comp/base/pkg/type_pack.vhd"

set RX_CALYPTE_BASE           "$ENTITY_BASE/comp/rx"
set TX_CALYPTE_BASE           "$ENTITY_BASE/comp/tx"
set MFB_FIFOX_BASE            "$OFM_PATH/comp/mfb_tools/storage/fifox"
set MI_SPLITTER_PLUS_GEN_BASE "$OFM_PATH/comp/mi_tools/splitter_plus_gen"

lappend COMPONENTS [ list "RX_DMA_CALYPTE"       $RX_CALYPTE_BASE           "FULL"]
lappend COMPONENTS [ list "TX_DMA_CALYPTE"       $TX_CALYPTE_BASE           "FULL"]
lappend COMPONENTS [ list "MFB_FIFOX"            $MFB_FIFOX_BASE            "FULL"]
lappend COMPONENTS [ list "MI_SPLITTER_PLUS_GEN" $MI_SPLITTER_PLUS_GEN_BASE "FULL"]

lappend MOD "$ENTITY_BASE/dma_calypte.vhd"
lappend MOD "$ENTITY_BASE/DevTree.tcl"
