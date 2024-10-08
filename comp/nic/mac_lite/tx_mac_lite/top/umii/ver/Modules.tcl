# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set SV_BASE            "$OFM_PATH/comp/ver"
set SV_MFB_BASE        "$OFM_PATH/comp/mfb_tools/ver"
set SV_MI32_TOOLS_BASE "$OFM_PATH/comp/mi_tools/ver"
set SV_MII_TOOLS_BASE  "$OFM_PATH/comp/nic/ver"

set COMPONENTS [list \
    [ list "SV_MFB"   $SV_MFB_BASE        "FULL"] \
    [ list "SV_MI32"  $SV_MI32_TOOLS_BASE "FULL"] \
    [ list "SV_BASE"  $SV_BASE            "FULL"] \
    [ list "SV_MII"   $SV_MII_TOOLS_BASE  "FULL"] \
]
set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
