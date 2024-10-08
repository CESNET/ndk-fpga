# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2009 CESNET
# Author: Jan Stourac   <xstour03@stud.fit.vutbr.cz>
#         Jakub Cabal   <jakubcabal@gmail.com>
#         Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#

global SYNTH_FLAGS

set MI32_ASYNC_HANDSHAKE_BASE "$OFM_PATH/comp/mi_tools/async"

set COMPONENTS [list [ list "MI32_ASYNC_HANDSHAKE" $MI32_ASYNC_HANDSHAKE_BASE "FULL" ]]

set MOD "$MOD $ENTITY_BASE/tsu_adder_ent.vhd"

if {[info exists SYNTH_FLAGS(TOOL)] && $SYNTH_FLAGS(TOOL) == "quartus"} {
    set MOD "$MOD $ENTITY_BASE/tsu_adder_common.vhd"
} else {
    set MOD "$MOD $ENTITY_BASE/tsu_adder_xilinx.vhd"
}

set MOD "$MOD $ENTITY_BASE/tsu_gen_core.vhd"
