# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2012 CESNET
# Author: Lukas Kekely  <kekely@cesnet.cz>
#         Jakub Cabal   <jakubcabal@gmail.com>
#         Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#

global SYNTH_FLAGS

set TSU_CORE_BASE             "$ENTITY_BASE/comp/tsu_gen_core"
set MI32_ASYNC_HANDSHAKE_BASE "$OFM_PATH/comp/mi_tools/async"
set ASYNC_RESET_BASE          "$OFM_PATH/comp/base/async/reset"
set ASYNC_HANDSHAKE_BASE      "$OFM_PATH/comp/base/async/bus_handshake"
set ALU                       "$OFM_PATH/comp/base/logic/alu"

# packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/tsu_gen_ent.vhd"
set MOD "$MOD $ENTITY_BASE/mult_1e9_ent.vhd"

# components
if {[info exists SYNTH_FLAGS(TOOL)] && $SYNTH_FLAGS(TOOL) == "quartus"} {

    set COMPONENTS [ list \
        [ list "TSU_CORE"             $TSU_CORE_BASE             "FULL" ] \
        [ list "MI32_ASYNC_HANDSHAKE" $MI32_ASYNC_HANDSHAKE_BASE "FULL" ] \
        [ list "ASYNC_RESET"          $ASYNC_RESET_BASE          "FULL" ] \
        [ list "ASYNC_BUS_HANDSHAKE"  $ASYNC_HANDSHAKE_BASE      "FULL" ] \
    ]
    set MOD "$MOD $ENTITY_BASE/mult_1e9_empty.vhd"

} else {

    set COMPONENTS [ list \
        [ list "TSU_CORE"             $TSU_CORE_BASE             "FULL"      ] \
        [ list "MI32_ASYNC_HANDSHAKE" $MI32_ASYNC_HANDSHAKE_BASE "FULL"      ] \
        [ list "ASYNC_RESET"          $ASYNC_RESET_BASE          "FULL"      ] \
        [ list "ASYNC_BUS_HANDSHAKE"  $ASYNC_HANDSHAKE_BASE      "FULL"      ] \
        [ list "ALU_DSP"              $ALU                       "STRUCTUAL" ] \
    ]
    set MOD "$MOD $ENTITY_BASE/mult_1e9.vhd"

}

# mods
set MOD "$MOD $ENTITY_BASE/tsu_convertor.vhd"
set MOD "$MOD $ENTITY_BASE/tsu_pps_processing.vhd"
set MOD "$MOD $ENTITY_BASE/tsu_gen_arch.vhd"
set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
