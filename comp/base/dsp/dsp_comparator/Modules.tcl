# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set OFM_BASE "$OFM_PATH/comp/base"

set XILINX_CMP_BASE "$OFM_BASE/logic/cmp"
set INTEL_CMP_BASE  "$OFM_BASE/dsp/dsp_comparator_intel"

set COMPONENTS [list \
    [list "DSP_CMP_XILINX" $XILINX_CMP_BASE "STRUCTURAL" ] \
    [list "DSP_CMP_INTEL"  $INTEL_CMP_BASE  "FULL"       ] \
]

lappend MOD "$ENTITY_BASE/dsp_comparator.vhd"
