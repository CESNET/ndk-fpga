# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PKG_BASE                 "$OFM_PATH/comp/base/pkg"
set SH_REG_BASE              "$OFM_PATH/comp/base/shreg/sh_reg_base"
set MFB_ENABLER_BASE         "$OFM_PATH/comp/mfb_tools/flow/enabler"
set MFB_FRAME_LNG_CHECK_BASE "$OFM_PATH/comp/mfb_tools/logic/frame_lng_check"
set MFB_SPEED_METER_BASE     "$OFM_PATH/comp/mfb_tools/logic/speed_meter"
set MFB_RECONFIG_BASE        "$OFM_PATH/comp/mfb_tools/flow/reconfigurator"
set MVB_SHAKEDOWN_BASE       "$OFM_PATH/comp/mvb_tools/flow/shakedown"
set LOCAL_COMP_BASE          "$ENTITY_BASE/comp"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/eth_hdr_pack.vhd"

set COMPONENTS [list \
    [list "SH_REG_BASE_STATIC"  $SH_REG_BASE                     "FULL"   ] \
    [list "MFB_ENABLER"         $MFB_ENABLER_BASE                "FULL"   ] \
    [list "MFB_FRAME_LNG_CHECK" $MFB_FRAME_LNG_CHECK_BASE        "FULL"   ] \
    [list "MFB_SPEED_METER"     $MFB_SPEED_METER_BASE            "FULL"   ] \
    [list "MFB_RECONFIG"        $MFB_RECONFIG_BASE               "FULL"   ] \
    [list "MVB_SHAKEDOWN"       $MVB_SHAKEDOWN_BASE              "FULL"   ] \
    [list "CRC_CUTTER"          $LOCAL_COMP_BASE/crc_cutter      "FULL"   ] \
    [list "CRC_CHECK"           $LOCAL_COMP_BASE/crc_check       $ARCHGRP ] \
    [list "MAC_CHECK"           $LOCAL_COMP_BASE/mac_check       "FULL"   ] \
    [list "TIMESTAMP"           $LOCAL_COMP_BASE/timestamp       "FULL"   ] \
    [list "STAT_UNIT"           $LOCAL_COMP_BASE/stat_unit       "FULL"   ] \
    [list "BUFFER"              $LOCAL_COMP_BASE/buffer          "FULL"   ] \
    [list "CTRL_UNIT"           $LOCAL_COMP_BASE/ctrl_unit       "FULL"   ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/rx_mac_lite.vhd"
set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
