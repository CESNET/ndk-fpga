# Modules.tcl: Local include tcl script
# Copyright (C) 2015 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
set ALU        "$OFM_PATH/comp/base/logic/alu"
set CMP        "$OFM_PATH/comp/base/logic/cmp"
set TO2N       "$OFM_PATH/comp/base/logic/barrel_shifter_dsp/to2n"

set COMPONENTS [ list \
                  [ list "ALU_DSP"              $ALU                  "STRUCTUAL" ] \
                  [ list "CMP_DSP"              $CMP                  "STRUCTUAL" ] \
                  [ list "TO2N"                 $TO2N                 "FULL" ] \
               ]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/low_shifter/dsp_shifter.vhd"
set MOD "$MOD $ENTITY_BASE/low_shifter/gen_dsp_shifter.vhd"
set MOD "$MOD $ENTITY_BASE/low_shifter/gen_dsp_shifter_rotate.vhd"
set MOD "$MOD $ENTITY_BASE/barrel_shifter_ent.vhd"
set MOD "$MOD $ENTITY_BASE/barrel_shifter_top.vhd"
set MOD "$MOD $ENTITY_BASE/barrel_shifter_rotate_top.vhd"
