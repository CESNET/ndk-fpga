# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set SV_MII_BASE      "$OFM_PATH/comp/nic/ver"
set SV_MFB_BASE      "$OFM_PATH/comp/mfb_tools/ver"
set SV_COMMON_BASE   "$OFM_PATH/comp/ver"

set COMPONENTS [list \
   [ list "SV_MII"    $SV_MII_BASE    "FULL"] \
   [ list "SV_MFB"    $SV_MFB_BASE    "FULL"] \
   [ list "SV_COMMON" $SV_COMMON_BASE "FULL"] \
]
set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
