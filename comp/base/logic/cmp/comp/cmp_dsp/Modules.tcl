# Modules.tcl: Local include tcl script
# Copyright (C) 2014 CESNET
# Author: Mario Kuka    <xkukam00@stud.fit.vutbr.cz>
#         Daniel kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

global SYNTH_FLAGS


set COMPONENTS [ list \
    [ list "MATH_PACK" "$OFM_PATH/comp/base/pkg" "MATH" ] \
]

set MOD "$MOD $ENTITY_BASE/cmp_dsp_ent.vhd"

if { [info exists SYNTH_FLAGS(TOOL)] && $SYNTH_FLAGS(TOOL) == "quartus" } {

    set MOD "$MOD $ENTITY_BASE/cmp_dsp_empty.vhd"

} else {

    set MOD "$MOD $ENTITY_BASE/cmp_decode.vhd"
    set MOD "$MOD $ENTITY_BASE/cmp48.vhd"
    set MOD "$MOD $ENTITY_BASE/cmp_dsp.vhd"

}
