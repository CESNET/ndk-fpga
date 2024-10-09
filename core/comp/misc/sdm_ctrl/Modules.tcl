# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Tomas Hak <xhakto01@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths
set MI2AVMM_BASE  "$OFM_PATH/comp/mi_tools/converters/mi2avmm"
set S10_ADC_BASE  "$OFM_PATH/comp/base/misc/adc_sensors"
set IDCOMP32_BASE "$OFM_PATH/comp/base/misc/id32"

# Files
lappend MOD "$ENTITY_BASE/sdm_ctrl_ent.vhd"

if {$ARCHGRP == "INTEL_SDM"} {
    lappend COMPONENTS [ list "MI2AVMM" $MI2AVMM_BASE "FULL" ]

    lappend MOD "$ENTITY_BASE/sdm_ctrl_arch.vhd"
    lappend MOD "$ENTITY_BASE/DevTree.tcl"

} elseif {$ARCHGRP == "S10_ADC"} {
    lappend COMPONENTS [ list "S10_ADC" $S10_ADC_BASE "FULL" ]

    lappend MOD "$ENTITY_BASE/sdm_ctrl_s10_adc.vhd"
} elseif {$ARCHGRP == "USP_IDCOMP"} {
    lappend COMPONENTS [ list "IDCOMP32" $IDCOMP32_BASE "USP" ]

    lappend MOD "$ENTITY_BASE/sdm_ctrl_usp_idcomp.vhd"
} else {
    lappend MOD "$ENTITY_BASE/sdm_ctrl_empty.vhd"
}
