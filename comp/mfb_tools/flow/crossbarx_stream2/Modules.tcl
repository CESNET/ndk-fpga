# Modules.tcl: script to compile single module
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Component paths
set SDP_BRAM_BASE        "$OFM_PATH/comp/base/mem/sdp_bram"
set MVB_MERGE_ITEMS_BASE "$OFM_PATH/comp/mvb_tools/flow/merge_items"
set MFB_FRAME_LNG_BASE   "$OFM_PATH/comp/mfb_tools/logic/frame_lng"
set TRANS_SORTER_BASE    "$OFM_PATH/comp/base/misc/trans_sorter"
set MVB_FIFOX_BASE       "$OFM_PATH/comp/mvb_tools/storage/fifox"
set PKT_PLANNER_BASE     "$OFM_PATH/comp/base/misc/packet_planner"
set CROSSBARX_BASE       "$OFM_PATH/comp/base/misc/crossbarx"
set OBUF_BASE            "$OFM_PATH/comp/mfb_tools/storage/crossbarx_output_buffer"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "SDP_BRAM"        $SDP_BRAM_BASE        "FULL" ]
lappend COMPONENTS [ list "TRANS_SORTER"    $TRANS_SORTER_BASE    "FULL" ]
lappend COMPONENTS [ list "MFB_FRAME_LNG"   $MFB_FRAME_LNG_BASE   "FULL" ]
lappend COMPONENTS [ list "MVB_MERGE_ITEMS" $MVB_MERGE_ITEMS_BASE "FULL" ]
lappend COMPONENTS [ list "MVB_FIFOX"       $MVB_FIFOX_BASE       "FULL" ]
lappend COMPONENTS [ list "PKT_PLANNER"     $PKT_PLANNER_BASE     "FULL" ]
lappend COMPONENTS [ list "CROSSBARX"       $CROSSBARX_BASE       "FULL" ]
lappend COMPONENTS [ list "OBUF"            $OBUF_BASE            "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/cxs2_rx_buf.vhd"
lappend MOD "$ENTITY_BASE/cxs2_tr_gen.vhd"
lappend MOD "$ENTITY_BASE/cxs2_tr_fifo.vhd"
lappend MOD "$ENTITY_BASE/crossbarx_stream2.vhd"
