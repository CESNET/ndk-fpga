# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set MI_SPLITTER_PLUS_GEN_BASE "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set GEN_LOOP_SWITCH_BASE      "$OFM_PATH/comp/mfb_tools/debug/gen_loop_switch"
set MFB_META_INS_BASE         "$OFM_PATH/comp/mfb_tools/flow/metadata_insertor"
set MFB_META_EXT_BASE         "$OFM_PATH/comp/mfb_tools/flow/metadata_extractor"
set DMA_WRAPPER_BASE          "$ENTITY_BASE/wrapper"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/pcie_meta_pack.vhd"

lappend MOD "$ENTITY_BASE/dma_ent.vhd"

# Common components
lappend COMPONENTS [list "MI_SPLITTER_PLUS_GEN" $MI_SPLITTER_PLUS_GEN_BASE "FULL"]
lappend COMPONENTS [list "GEN_LOOP_SWITCH"      $GEN_LOOP_SWITCH_BASE      "FULL"]

if {$ARCHGRP == "EMPTY" } {
    lappend MOD "$ENTITY_BASE/dma_empty_arch.vhd"
} else {
    # Architecture specific component
    lappend COMPONENTS [list "METADATA_INSERTOR"  $MFB_META_INS_BASE "FULL"  ]
    lappend COMPONENTS [list "METADATA_EXTRACTOR" $MFB_META_EXT_BASE "FULL"  ]
    lappend COMPONENTS [list "DMA_WRAPPER"        $DMA_WRAPPER_BASE  $ARCHGRP]

    # Source files for implemented component
    lappend MOD "$ENTITY_BASE/dma_full_arch.vhd"
    lappend MOD "$ENTITY_BASE/DevTree.tcl"
}
