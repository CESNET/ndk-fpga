# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jan Kubalek <kubalek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set DMA_MFB_GENERATOR_BASE    "$OFM_PATH/comp/mfb_tools/debug/dma_generator"
set MFB_FRAME_PLAYER_BASE     "$OFM_PATH/comp/mfb_tools/debug/frame_player"
set MFB_SPEED_METER_BASE      "$OFM_PATH/comp/mfb_tools/logic/speed_meter"
set MI32_ASYNC_HANDSHAKE_BASE "$OFM_PATH/comp/mi_tools/async"
set MI32_SPLITTER_BASE        "$OFM_PATH/comp/mi_tools/splitter_plus_gen"

set COMPONENTS [list \
    [ list "DMA_MFB_GENERATOR"    $DMA_MFB_GENERATOR_BASE                         "FULL" ] \
    [ list "MFB_FRAME_PLAYER"     $MFB_FRAME_PLAYER_BASE                          "FULL" ] \
    [ list "MFB_SPEED_METER"      $MFB_SPEED_METER_BASE                           "FULL" ] \
    [ list "MI32_ASYNC_HANDSHAKE" $MI32_ASYNC_HANDSHAKE_BASE                      "FULL" ] \
    [ list "MI32_SPLITTER"        $MI32_SPLITTER_BASE                             "FULL" ] \
    [ list "MVB_FIFOX"            "$OFM_PATH/comp/mvb_tools/storage/fifox"        "FULL" ] \
    [ list "MFB_FIFOX"            "$OFM_PATH/comp/mfb_tools/storage/fifox"        "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/gen_loop_switch.vhd"
set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
