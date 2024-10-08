# Modules.tcl: Local include tcl script
# Copyright (C) 2015 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set REGS       "$OFM_PATH/comp/base/logic/pipe_dsp"
set INSERT     "$OFM_PATH/comp/flu_tools/edit/packet_insert_bytes"
set EDITOR     "$OFM_PATH/comp/flu_tools/edit/packet_editor"
set F_PIPE     "$OFM_PATH/comp/flu_tools/flow/pipe"
set S_PIPE     "$OFM_PATH/comp/base/misc/pipe"

set COMPONENTS [ list \
                  [ list "PIPE_DSP"             $REGS                 "FULL" ] \
                  [ list "PACKET_INSERT"        $INSERT               "FULL" ] \
                  [ list "PACKET_EDITOR"        $EDITOR               "FULL" ] \
                  [ list "FLU_PIPE"             $F_PIPE               "FULL" ] \
                  [ list "PIPE"                 $S_PIPE               "FULL" ] \
               ]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $ENTITY_BASE/func.vhd"

set MOD "$MOD $ENTITY_BASE/packet_insert_editor_ent.vhd"
set MOD "$MOD $ENTITY_BASE/packet_insert_editor_arch.vhd"

if {$ARCHGRP == "SYNTH"} {
    lappend MOD "$ENTITY_BASE/synth/packet_insert_synt.vhd"
}
