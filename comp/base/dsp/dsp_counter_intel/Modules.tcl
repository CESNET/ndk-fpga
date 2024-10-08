# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

global SYNTH_FLAGS

# Set paths
set PKG_BASE "$OFM_PATH/comp/base/pkg"
set INTEL_CNT_COMP_BASE "$OFM_PATH/comp/base/dsp/dsp_counter_intel/comp"

lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

# Packages only for the simulation
lappend PACKAGES "$PKG_BASE/dma_bus_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/ver/vhdl_ver_tools/basics/basics_test_pkg.vhd"

lappend MOD "$ENTITY_BASE/dsp_counter_intel_ent.vhd"

# choose empty architecure when using Intel DSPs in Vivado
if {[info exists SYNTH_FLAGS(TOOL)] && $SYNTH_FLAGS(TOOL) == "vivado"} {
    lappend MOD "$ENTITY_BASE/dsp_counter_intel_empty.vhd"
} else {
    set COMPONENTS [list \
        [list "AGILEX_CNT"    "$INTEL_CNT_COMP_BASE/dsp_counter_stratix10" "STRUCT"] \
        [list "STRATIX10_CNT" "$INTEL_CNT_COMP_BASE/dsp_counter_agilex"    "STRUCT"] \
    ]

    lappend MOD "$ENTITY_BASE/dsp_counter_intel.vhd"
}
