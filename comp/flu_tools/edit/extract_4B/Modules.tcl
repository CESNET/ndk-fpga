# Modules.tcl: Local include tcl script
# Copyright (C) 2016 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set REGS       "$OFM_PATH/comp/base/logic/pipe_dsp"
set MUX        "$OFM_PATH/comp/base/logic/mux"
set DEMUX      "$OFM_PATH/comp/base/logic/demux"
set ALU        "$OFM_PATH/comp/base/logic/alu"
set CMP        "$OFM_PATH/comp/base/logic/cmp"
set MUX_DSP    "$OFM_PATH/comp/base/logic/mux_dsp"

set COMPONENTS [ list \
                  [ list "GEN_MUX"              $MUX                  "FULL" ] \
                  [ list "PIPE_DSP"             $REGS                 "FULL" ] \
                  [ list "GEN_DEMUX"            $DEMUX                "FULL" ] \
                  [ list "ALU_DSP"              $ALU                  "FULL" ] \
                  [ list "CMP_DSP"              $CMP                  "FULL" ] \
                  [ list "MUX_DSP"              $MUX_DSP              "FULL" ] \
               ]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/get_block.vhd"
set MOD "$MOD $ENTITY_BASE/offset_control.vhd"
set MOD "$MOD $ENTITY_BASE/extract_4B_ent.vhd"
set MOD "$MOD $ENTITY_BASE/extract_4B_arch.vhd"

if {$ARCHGRP == "SYNTH"} {
    lappend MOD "$ENTITY_BASE/synth/extract_4B_synt.vhd"
}
