# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE "$OFM_PATH/comp/base/pkg"
set INTEL_CNT_COMP_BASE "$ENTITY_BASE/comp"

lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

lappend MOD "$ENTITY_BASE/dsp_counter_intel_ent.vhd"

# choose empty architecure when using Intel DSPs in Vivado
if {"altera" in $PLATFORM_TAGS} {
    set COMPONENTS [list \
        [list "STRATIX10_CNT"   "$INTEL_CNT_COMP_BASE/dsp_counter_stratix10" "STRUCT"] \
        [list "AGILEX_CNT"      "$INTEL_CNT_COMP_BASE/dsp_counter_agilex"    "STRUCT"] \
    ]

    lappend MOD "$ENTITY_BASE/dsp_counter_intel.vhd"
} else {
    lappend MOD "$ENTITY_BASE/dsp_counter_intel_empty.vhd"
}
