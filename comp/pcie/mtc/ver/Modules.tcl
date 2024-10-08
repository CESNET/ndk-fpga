# Modules.tcl: script to compile single module
# Copyright (C) 2018 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause



# List of modules

set COMPONENTS [ list \
   [ list "MTC"              $OFM_PATH/comp/pcie/mtc       "SRC" ] \
   [ list "CONNECTION_BLOCK" $OFM_PATH/comp/pcie/others/connection_block/ "FULL" ] \
   [ list "SV_COMMON"        $OFM_PATH/comp/ver            "FULL" ] \
   [ list "SV_AXI"           $OFM_PATH/comp/ver/pcie       "FULL" ] \
   [ list "MI"               $OFM_PATH/comp/mi_tools/ver "UNIFIED" ] \
]

set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"

set MOD "$MOD $ENTITY_BASE/tbench/pcie/pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/scoreboard/pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
set MOD "$MOD $ENTITY_BASE/tbench/testbench.sv"
