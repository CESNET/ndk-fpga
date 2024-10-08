# Modules.tcl: Local include tcl script
# Copyright (C) 2015 CESNET
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

set MOD "$MOD $ENTITY_BASE/comp/data_replace.vhd"
set MOD "$MOD $ENTITY_BASE/comp/flu_four_bytes_edit.vhd"
set MOD "$MOD $ENTITY_BASE/comp/packet_editor_ent.vhd"
set MOD "$MOD $ENTITY_BASE/comp/packet_editor_arch.vhd"
set MOD "$MOD $ENTITY_BASE/packet_editor_top_ent.vhd"
set MOD "$MOD $ENTITY_BASE/packet_editor_top_arch.vhd"

if {$ARCHGRP == "SYNTH"} {
    lappend MOD "$ENTITY_BASE/synth/packet_editor_synt.vhd"
}
