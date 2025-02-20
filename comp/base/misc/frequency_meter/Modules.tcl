# Modules.tcl: Script to compile single module
# Copyright (C) 2025 CESNET
# Author: Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set ASYNC_BASE "$OFM_PATH/comp/base/async"
set DSP_BASE   "$OFM_PATH/comp/base/dsp"
set FIFO_BASE  "$OFM_PATH/comp/base/fifo"
set LOGIC_BASE "$OFM_PATH/comp/base/logic"
set MGMT_BASE  "$OFM_PATH/comp/nic/eth_phy/comp/mgmt"

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [list "ASYNC_OPEN_LOOP"  "$ASYNC_BASE/open_loop"    "FULL" ]
lappend COMPONENTS [list "ASYNC_RESET"      "$ASYNC_BASE/reset"        "FULL" ]
lappend COMPONENTS [list "DSP_COUNTER"      "$DSP_BASE/dsp_counter"    "FULL" ]
lappend COMPONENTS [list "ASFIFOX"          "$FIFO_BASE/asfifox"       "FULL" ]
lappend COMPONENTS [list "PULSE_EXTEND"     $MGMT_BASE                 "FULL" ]
lappend COMPONENTS [list "EDGE_DETECT"      "$LOGIC_BASE/edge_detect"  "FULL" ]

lappend MOD "$ENTITY_BASE/frequency_meter_core.vhd"
lappend MOD "$ENTITY_BASE/frequency_meter.vhd"

lappend MOD "$ENTITY_BASE/DevTree.tcl"
