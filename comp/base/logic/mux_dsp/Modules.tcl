# Modules.tcl: Local include tcl script
# Copyright (C) 2014 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set PIPE      "$OFM_PATH/comp/base/logic/pipe_dsp"

set COMPONENTS [ list \
                  [ list "PIPE_DSP"              $PIPE                  "STRUCTUAL"  ] \
               ]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $ENTITY_BASE/mux_lvl_func.vhd"

set MOD "$MOD $ENTITY_BASE/mux48.vhd"
set MOD "$MOD $ENTITY_BASE/mux_dsp.vhd"
set MOD "$MOD $ENTITY_BASE/mux_dsp_gen_low.vhd"
set MOD "$MOD $ENTITY_BASE/mux_dsp_gen.vhd"
