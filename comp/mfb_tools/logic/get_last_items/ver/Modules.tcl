# Modules.tcl: Components include script
# Copyright (C) 2026 CESNET z.s.p.o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set SV_MFB_BASE      "$OFM_PATH/comp/mfb_tools/ver"
set SV_MVB_BASE      "$OFM_PATH/comp/mvb_tools/ver"

lappend COMPONENTS [ list "SV_MFB"   $SV_MFB_BASE  "FULL"]
lappend COMPONENTS [ list "SV_MVB"   $SV_MVB_BASE  "FULL"]

lappend MOD "$ENTITY_BASE/tbench/test_pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/test.sv"
