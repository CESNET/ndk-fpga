# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/pcie_meta_pack.vhd"

set META_EXTRACTOR_BASE       "$ENTITY_BASE/comp/metadata_extractor"
set CHAN_START_STOP_CTRL_BASE "$ENTITY_BASE/comp/chan_start_stop_ctrl"
set SW_MANAGER_BASE           "$ENTITY_BASE/comp/software_manager"
set PACKET_DISPATCHER_BASE    "$ENTITY_BASE/comp/packet_dispatcher"
set PCIE_TRANS_BUFFER_BASE    "$ENTITY_BASE/comp/pcie_trans_buffer"
set MVB_FIFOX_BASE            "$OFM_PATH/comp/mvb_tools/storage/fifox"
set FIFOX_MULTI_BASE          "$OFM_PATH/comp/base/fifo/fifox_multi"

lappend COMPONENTS [ list "TX_DMA_METADATA_EXTRACTOR"   $META_EXTRACTOR_BASE       "FULL"]
lappend COMPONENTS [ list "TX_DMA_CHAN_START_STOP_CTRL" $CHAN_START_STOP_CTRL_BASE "FULL"]
lappend COMPONENTS [ list "TX_DMA_SW_MANAGER"           $SW_MANAGER_BASE           "FULL"]
lappend COMPONENTS [ list "TX_DMA_PKT_DISPATCHER"       $PACKET_DISPATCHER_BASE    "FULL"]
lappend COMPONENTS [ list "TX_DMA_PCIE_TRANS_BUFFER"    $PCIE_TRANS_BUFFER_BASE    "FULL"]
lappend COMPONENTS [ list "MVB_FIFOX"                   $MVB_FIFOX_BASE            "FULL"]
lappend COMPONENTS [ list "FIFOX_MULTI"                 $FIFOX_MULTI_BASE          "FULL"]

lappend MOD "$ENTITY_BASE/tx_dma_calypte.vhd"
