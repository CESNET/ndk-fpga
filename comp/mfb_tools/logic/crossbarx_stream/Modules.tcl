# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE           "$OFM_PATH/comp/base/pkg"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set CROSSBARX_BASE     "$OFM_PATH/comp/base/misc/crossbarx"
set OBUF_BASE          "$OFM_PATH/comp/mfb_tools/storage/crossbarx_output_buffer"

set COMPONENTS [list \
    [list "CROSSBARX"     "$CROSSBARX_BASE"                          "FULL" ] \
    [list "TRANS_FIFO"    "$CROSSBARX_BASE/comp/trans_fifo"          "FULL" ] \
    [list "PKT_PLANNER"   "$OFM_PATH/comp/base/misc/packet_planner"  "FULL" ] \
    [list "SDP_BRAM"      "$OFM_PATH/comp/base/mem/sdp_bram"         "FULL" ] \
    [list "ASFIFOX"       "$OFM_PATH/comp/base/fifo/asfifox"         "FULL" ] \
    [list "FIFOX_MULTI"   "$OFM_PATH/comp/base/fifo/fifox_multi"     "FULL" ] \
    [list "TRANS_GEN"     "$ENTITY_BASE/comp/trans_gen"              "FULL" ] \
    [list "OUTPUT_BUF"    "$OBUF_BASE"                               "FULL" ] \
    [list "MFB_FRAME_LNG" "$OFM_PATH/comp/mfb_tools/logic/frame_lng"     "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/crossbarx_stream.vhd"
