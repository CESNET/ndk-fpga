# Modules.tcl: Components include script
# Copyright (C) 2024 BrnoLogic, Ltd.
# Author(s): Radek Hajek <hajek@brnologic.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SV_COMP_BASE   "$ENTITY_BASE/../../../.."

lappend COMPONENTS [ list "SV_MFB"   $SV_COMP_BASE/mfb_tools/ver  "FULL"]
lappend COMPONENTS [ list "SV_AXI"   $SV_COMP_BASE/ver/axi        "FULL"]

lappend MOD "$ENTITY_BASE/tbench/test_pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/test.sv"
