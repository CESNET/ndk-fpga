# Modules.tcl: Local include tcl script
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author: Vlastimil Kosar <kosar@dyna-nic.com>, 2024
#
# SPDX-License-Identifier: BSD-3-Clause

global SYNTH_FLAGS

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set COMPONENTS [ list \
    [ list "MI2AXI4"        "$OFM_PATH/comp/mi_tools/converters/mi2axi4"      "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/versal_fpga_id.vhd"
