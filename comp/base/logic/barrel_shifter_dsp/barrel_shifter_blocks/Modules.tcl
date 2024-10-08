# Modules.tcl: Local include tcl script
# Copyright (C) 2015 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
set ALU        "$OFM_PATH/comp/base/logic/alu"
set CMP        "$OFM_PATH/comp/base/logic/cmp"
set TO2N       "$OFM_PATH/comp/base/logic/barrel_shifter_dsp/to2n"
set SHIFTER    "$OFM_PATH/comp/base/logic/barrel_shifter_dsp/barrel_shifter"

set COMPONENTS [ list \
                  [ list "ALU_DSP"              $ALU                  "STRUCTUAL" ] \
                  [ list "TO2N"                 $TO2N                 "FULL" ] \
                  [ list "BAREL_SHITER_DSP"     $SHIFTER              "shift_arch" ] \
               ]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/barrel_shifter_blocks_ent.vhd"
set MOD "$MOD $ENTITY_BASE/barrel_shifter_blocks_top.vhd"
