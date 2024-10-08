# Modules.tcl: Local include tcl script
# Copyright (C) 2014 CESNET
# Author: Mario Kuka    <xkukam00@stud.fit.vutbr.cz>
#         Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

global SYNTH_FLAGS

# Set paths
set MOD "$MOD $ENTITY_BASE/count_dsp_ent.vhd"

if { [info exists SYNTH_FLAGS(TOOL)] && $SYNTH_FLAGS(TOOL) == "quartus" } {

    set MOD "$MOD $ENTITY_BASE/count_dsp_empty.vhd"

} else {

    set MOD "$MOD $ENTITY_BASE/count48.vhd"
    set MOD "$MOD $ENTITY_BASE/count_dsp.vhd"

    # COUNT_TOP with input and output registers for measurements
    # set MOD "$MOD $ENTITY_BASE/synth/count_top.vhd"

}
