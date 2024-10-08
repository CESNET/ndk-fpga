# Modules.tcl: Local include tcl script
# Copyright (C) 2014 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MOD "$MOD $ENTITY_BASE/alu48.vhd"
set MOD "$MOD $ENTITY_BASE/alu_dsp.vhd"
set PIPE   "$OFM_PATH/comp/base/logic/pipe_dsp"

set COMPONENTS [ list \
                  [ list "PIPE"                 $PIPE                 "FULL" ] \
               ]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

if {$ARCHGRP == "SYNTH"} {
    lappend MOD "$ENTITY_BASE/synth/alu_dsp_top.vhd"
}
