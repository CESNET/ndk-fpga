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
set F_PIPE     "$OFM_PATH/comp/flu_tools/flow/pipe"
set S_PIPE     "$OFM_PATH/comp/base/misc/pipe"

set COMPONENTS [ list \
                  [ list "GEN_MUX"              $MUX                  "FULL" ] \
                  [ list "PIPE_DSP"             $REGS                 "FULL" ] \
                  [ list "GEN_DEMUX"            $DEMUX                "FULL" ] \
                  [ list "ALU_DSP"              $ALU                  "FULL" ] \
                  [ list "CMP_DSP"              $CMP                  "FULL" ] \
                  [ list "MUX_DSP"              $MUX_DSP              "FULL" ] \
                  [ list "FLU_PIPE"             $F_PIPE               "FULL" ] \
                  [ list "PIPE"                 $S_PIPE               "FULL" ] \
               ]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/comp/flu_split.vhd"
set MOD "$MOD $ENTITY_BASE/comp/high_eop_pos.vhd"
set MOD "$MOD $ENTITY_BASE/comp/offset_control.vhd"
set MOD "$MOD $ENTITY_BASE/comp/insert_offset.vhd"
set MOD "$MOD $ENTITY_BASE/comp/data_shifter.vhd"
set MOD "$MOD $ENTITY_BASE/comp/block_insert.vhd"
set MOD "$MOD $ENTITY_BASE/comp/insert.vhd"
set MOD "$MOD $ENTITY_BASE/comp/packet_insert.vhd"
set MOD "$MOD $ENTITY_BASE/packet_insert_top.vhd"
