# Modules.tcl: Local include tcl script
# Copyright (C) 2014 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
set ALU        "$OFM_PATH/comp/base/logic/alu"
set PIPE       "$OFM_PATH/comp/base/logic/pipe_dsp"

set COMPONENTS [ list \
                  [ list "ALU_DSP"              $ALU                  "STRUCTUAL" ] \
                  [ list "PIPE"                 $PIPE                 "FULL" ] \
               ]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/mul48.vhd"
set MOD "$MOD $ENTITY_BASE/mul_dsp_ent.vhd"
set MOD "$MOD $ENTITY_BASE/mul_dsp_arch.vhd"

if {$ARCHGRP == "SYNTH"} {
    lappend MOD "$ENTITY_BASE/synth/mul48_top.vhd"
}
