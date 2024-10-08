# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE           "$OFM_PATH/comp/base/pkg"
set FIFOX_BASE         "$OFM_PATH/comp/base/fifo/fifox"
set MVB_ASFIFOX_BASE   "$OFM_PATH/comp/mvb_tools/storage/asfifox"
set MFB_PD_ASFIFO_BASE "$OFM_PATH/comp/mfb_tools/storage/pd_asfifo"
set MFB_FRAME_LNG_BASE "$OFM_PATH/comp/mfb_tools/logic/frame_lng"
set MFB_RECONFIG_BASE  "$OFM_PATH/comp/mfb_tools/flow/reconfigurator"
set MFB_CX_STREAM_BASE "$OFM_PATH/comp/mfb_tools/logic/crossbarx_stream"
set LCOMP_BASE         "$ENTITY_BASE/comp"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
   [list "FIFOX"         $FIFOX_BASE              "FULL"   ] \
   [list "MVB_ASFIFOX"   $MVB_ASFIFOX_BASE        "FULL"   ] \
   [list "MFB_PD_ASFIFO" $MFB_PD_ASFIFO_BASE      "FULL"   ] \
   [list "MFB_FRAME_LNG" $MFB_FRAME_LNG_BASE      "FULL"   ] \
   [list "MFB_RECONFIG"  $MFB_RECONFIG_BASE       "FULL"   ] \
   [list "CRC_GEN"       "$LCOMP_BASE/crc_gen"    $ARCHGRP ] \
   [list "CRC_INSERT"    "$LCOMP_BASE/crc_insert" "FULL"   ] \
   [list "SPACER"        $MFB_CX_STREAM_BASE      "FULL"   ] \
   [list "STAT_UNIT"     "$LCOMP_BASE/stat_unit"  "FULL"   ] \
   [list "ADDR_DEC"      "$LCOMP_BASE/addr_dec"   "FULL"   ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/tx_mac_lite.vhd"
set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
