# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/pcie_meta_pack.vhd"

set PCIE_CQ_HDR_DEPARSER_BASE  "$OFM_PATH/comp/pcie/others/hdr_gen"
set MFB_CUTTER_BASE            "$OFM_PATH/comp/mfb_tools/flow/cutter_simple"
set MFB_AUXILIARY_SIGNALS_BASE "$OFM_PATH/comp/mfb_tools/logic/auxiliary_signals"
set PCIE_BYTE_EN_DECODER_BASE  "$OFM_PATH/comp/pcie/logic/byte_en_decoder"
set PCIE_BYTE_COUNT_BASE       "$OFM_PATH/comp/pcie/logic/byte_count"

lappend COMPONENTS [ list "PCIE_CQ_HDR_DEPARSER"  $PCIE_CQ_HDR_DEPARSER_BASE  "FULL"]
lappend COMPONENTS [ list "MFB_CUTTER_SIMPLE"     $MFB_CUTTER_BASE            "FULL"]
lappend COMPONENTS [ list "MFB_AUXILIARY_SIGNALS" $MFB_AUXILIARY_SIGNALS_BASE "FULL"]
lappend COMPONENTS [ list "PCIE_BYTE_EN_DECODER"  $PCIE_BYTE_EN_DECODER_BASE  "FULL"]
lappend COMPONENTS [ list "PCIE_BYTE_COUNT"       $PCIE_BYTE_COUNT_BASE       "FULL"]

lappend MOD "$ENTITY_BASE/tx_dma_metadata_extractor.vhd"
