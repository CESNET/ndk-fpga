# Modules.tcl: Local include tcl script
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author: Vlastimil Kosar <kosar@dyna-nic.com>, 2025
#
# SPDX-License-Identifier: BSD-3-Clause

global SYNTH_FLAGS

set MI_BASE "$OFM_PATH/comp/mi_tools"

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set COMPONENTS [ list \
    [ list "VERSAL_PS_ACCESS"     "$ENTITY_BASE/comp/versal_ps_access"      "FULL" ] \
    [ list "VERSAL_FPGA_ID"       "$ENTITY_BASE/comp/versal_fpga_id"        "FULL" ] \
    [ list "VERSAL_AXI_SWITCH"    "$ENTITY_BASE/comp/versal_axi_switch"     "FULL" ] \
    [ list "SYNC_FPGA_ID"         "$ENTITY_BASE/comp/sync_fpga_id"          "FULL" ] \
    [ list "AXI4LITE2MI"          "$MI_BASE/converters/axi4lite2mi"         "FULL" ] \
    [ list "MI_ASYNC"             "$MI_BASE/async"                          "FULL" ] \
    [ list "SH_REG_BASE_STATIC"   "$OFM_PATH/comp/base/shreg/sh_reg_base"   "FULL" ] \
    [ list "ASYNC_OPEN_LOOP"      "$OFM_PATH/comp/base/async/open_loop"     "FULL" ] \
    [ list "ASYNC_OPEN_LOOP_SMD"  "$OFM_PATH/comp/base/async/open_loop_smd" "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/versal_ps_ctrl.vhd"
lappend MOD "$ENTITY_BASE/DevTree.tcl"
