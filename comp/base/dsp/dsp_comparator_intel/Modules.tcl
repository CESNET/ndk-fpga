# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

global SYNTH_FLAGS

# Set paths

set PKG_BASE       "$OFM_PATH/comp/base/pkg"
set AGILEX_BASE    "$OFM_PATH/comp/base/dsp/dsp_comparator_intel/comp/dsp_comparator_agilex"
set STRATIX10_BASE "$OFM_PATH/comp/base/dsp/dsp_comparator_intel/comp/dsp_comparator_stratix10"

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/dma_bus_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/ver/vhdl_ver_tools/basics/basics_test_pkg.vhd"

set MOD "$MOD $ENTITY_BASE/dsp_comparator_intel_ent.vhd"

if { [info exists SYNTH_FLAGS(TOOL)] && $SYNTH_FLAGS(TOOL) == "vivado" } {

    set MOD "$MOD $ENTITY_BASE/dsp_comparator_intel_empty.vhd"

} else {

    set COMPONENTS [list \
        [list "AGILEX_COMP"    $AGILEX_BASE    "FULL"] \
        [list "STRATIX10_COMP" $STRATIX10_BASE "FULL"] \
    ]

    set MOD "$MOD $ENTITY_BASE/dsp_comparator_intel.vhd"

}
