# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET
# Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


# Set paths

set SV_MVB_BASE   "$OFM_PATH/comp/mvb_tools/ver"

set COMPONENTS [list \
      [ list "SV_MVB"   $SV_MVB_BASE  "FULL"] \
]
set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
