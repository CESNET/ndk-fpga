# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET z. s. p. o.
# Author: Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PKG_BASE            "$OFM_PATH/comp/base/pkg"

set MVB_TOOLS_BASE     "$OFM_PATH/comp/mvb_tools"
set MFB_TOOLS_BASE     "$OFM_PATH/comp/mfb_tools"
set SUBCOMP_BASE       "$ENTITY_BASE/comp"

lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"
lappend PACKAGES "$PKG_BASE/dma_bus_pack.vhd"

# list of sub-components
lappend COMPONENTS [ list "MVB_SFIFOX"          "$MVB_TOOLS_BASE/storage/fifox"              "FULL" ]
lappend COMPONENTS [ list "MVB_ASFIFOX"         "$MVB_TOOLS_BASE/storage/asfifox"            "FULL" ]
lappend COMPONENTS [ list "MVB_SHAKEDOWN"       "$MVB_TOOLS_BASE/flow/shakedown"             "FULL" ]
lappend COMPONENTS [ list "MFB_FIFOX"           "$MFB_TOOLS_BASE/storage/fifox"              "FULL" ]
lappend COMPONENTS [ list "MFB_ASFIFOX"         "$MFB_TOOLS_BASE/storage/asfifox"            "FULL" ]
lappend COMPONENTS [ list "MFB_MERGER"          "$MFB_TOOLS_BASE/flow/merger"                "FULL" ]
lappend COMPONENTS [ list "MFB_SPLITTER"        "$MFB_TOOLS_BASE/flow/splitter"              "FULL" ]
lappend COMPONENTS [ list "MFB_TRANSFORMER"     "$MFB_TOOLS_BASE/flow/transformer"           "FULL" ]
lappend COMPONENTS [ list "MFB_ASFIFO_512to256" "$SUBCOMP_BASE/mfb_asfifo_512to256"          "FULL" ]
lappend COMPONENTS [ list "MFB_ASFIFO_256to512" "$SUBCOMP_BASE/mfb_asfifo_256to512"          "FULL" ]
lappend COMPONENTS [ list "SUM_ONE"             "$OFM_PATH/comp/base/logic/sum_one"          "FULL" ]
lappend COMPONENTS [ list "PIPE_TREE_ADDER"     "$OFM_PATH/comp/base/logic/pipe_tree_adder"  "FULL" ]
lappend COMPONENTS [ list "ASFIFOX"             "$OFM_PATH/comp/base/fifo/asfifox"           "FULL" ]
lappend COMPONENTS [ list "DMA2PCIE"            "$SUBCOMP_BASE/dma2pcie_hdr_transform"       "FULL" ]
lappend COMPONENTS [ list "CODAPA_CHECKER"      "$SUBCOMP_BASE/codapa_checker"               "FULL" ]
lappend COMPONENTS [ list "HDR_DATA_MERGE"      "$SUBCOMP_BASE/hdr_data_merge"               "FULL" ]
lappend COMPONENTS [ list "MFB2PCIE_AXI"        "$SUBCOMP_BASE/mfb2pcie_axi"                 "FULL" ]
lappend COMPONENTS [ list "TAG_MANAGER"         "$SUBCOMP_BASE/tag_manager"                  "FULL" ]
lappend COMPONENTS [ list "PCIE_AXI2MFB"        "$SUBCOMP_BASE/pcie_axi2mfb"                 "FULL" ]
lappend COMPONENTS [ list "MFB_FIFO"            "$MFB_TOOLS_BASE/storage/fifo_bram_xilinx"   "FULL" ]
lappend COMPONENTS [ list "MFB_GET_ITEMS"       "$MFB_TOOLS_BASE/logic/get_items"            "FULL" ]
lappend COMPONENTS [ list "PCIE2DMA"            "$SUBCOMP_BASE/pcie2dma_hdr_transform"       "FULL" ]
lappend COMPONENTS [ list "FRAME_ERASER"        "$SUBCOMP_BASE/frame_eraser_upto96bits"      "FULL" ]
lappend COMPONENTS [ list "STORAGE_FIFO"        "$SUBCOMP_BASE/storage_fifo"                 "FULL" ]
lappend COMPONENTS [ list "MVB_PIPE"            "$MVB_TOOLS_BASE/flow/pipe"                  "FULL" ]
lappend COMPONENTS [ list "MFB_PIPE"            "$MFB_TOOLS_BASE/flow/pipe"                  "FULL" ]
lappend COMPONENTS [ list "CUTTER"              "$MFB_TOOLS_BASE/flow/cutter_simple"         "FULL" ]

# entity and architecture
lappend MOD "$ENTITY_BASE/ptc_ent.vhd"
lappend MOD "$ENTITY_BASE/ptc_full.vhd"
lappend MOD "$ENTITY_BASE/ptc_wrapper.vhd"
