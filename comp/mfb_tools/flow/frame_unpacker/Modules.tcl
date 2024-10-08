# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set MVB_LAST_VLD_BASE        "$OFM_PATH/comp/mvb_tools/aggregate/last_vld"
set MVB_MERGE_ITEMS_BASE     "$OFM_PATH/comp/mvb_tools/flow/merge_items"
set GEN_MUX_ONEHOT_BASE      "$OFM_PATH/comp/base/logic/mux"
set FIFOX_MULTI_BASE         "$OFM_PATH/comp/base/fifo/fifox_multi"
set MFB_GET_ITEMS_BASE       "$OFM_PATH/comp/mfb_tools/logic/get_items"
set MFB_CUTTER_SIMPLE_BASE   "$OFM_PATH/comp/mfb_tools/flow/cutter_simple"
set META_INSERTOR_BASE       "$OFM_PATH/comp/mfb_tools/flow/metadata_insertor"
set MFB_FIFOX_BASE           "$OFM_PATH/comp/mfb_tools/storage/fifox"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "MVB_LAST_VLD"      $MVB_LAST_VLD_BASE      "FULL" ]
lappend COMPONENTS [ list "MVB_MERGE_ITEMS"   $MVB_MERGE_ITEMS_BASE   "FULL" ]
lappend COMPONENTS [ list "GEN_MUX_ONEHOT"    $GEN_MUX_ONEHOT_BASE    "FULL" ]
lappend COMPONENTS [ list "FIFOX_MULTI"       $FIFOX_MULTI_BASE       "FULL" ]
lappend COMPONENTS [ list "MFB_GET_ITEMS"     $MFB_GET_ITEMS_BASE     "FULL" ]
lappend COMPONENTS [ list "MFB_CUTTER_SIMPLE" $MFB_CUTTER_SIMPLE_BASE "FULL" ]
lappend COMPONENTS [ list "META_INSERTOR"     $META_INSERTOR_BASE     "FULL" ]
lappend COMPONENTS [ list "MFB_FIFOX"         $MFB_FIFOX_BASE         "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/offset_processor.vhd"
lappend MOD "$ENTITY_BASE/sof_creator.vhd"
lappend MOD "$ENTITY_BASE/frame_unpacker.vhd"
lappend MOD "$ENTITY_BASE/DevTree.tcl"

