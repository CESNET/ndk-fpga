# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-CLause

set SV_MFB_BASE   "$ENTITY_BASE/../../../../../../../../comp/mfb_tools/ver"

set COMPONENTS [list \
      [ list "SV_MFB"   $SV_MFB_BASE  "FULL"] \
]
set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
