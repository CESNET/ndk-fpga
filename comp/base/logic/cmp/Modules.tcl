# Modules.tcl: Local include tcl script
# Copyright (C) 2014 CESNET
# Author: Mario Kuka    <xkukam00@stud.fit.vutbr.cz>
#         Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set COMPONENTS [ list \
    [ list "MATH_PACK" "$OFM_PATH/comp/base/pkg"   "MATH"       ] \
    [ list "CMP_DSP"   "$ENTITY_BASE/comp/cmp_dsp" "STRUCTURAL" ] \
]

set MOD "$MOD $ENTITY_BASE/cmp_top.vhd"

# CMP_SYNTH with input and output registers for measurements
#set MOD "$MOD $ENTITY_BASE/synth/cmp_synth.vhd"
