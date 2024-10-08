# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set SV_MFB_BASE "$OFM_PATH/comp/mfb_tools/ver"
set SV_MVB_BASE "$OFM_PATH/comp/mvb_tools/ver"

set COMPONENTS [list \
   [ list "SV_MFB" $SV_MFB_BASE "FULL"] \
   [ list "SV_MVB" $SV_MVB_BASE "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/tbench/dut_wrapper.vhd"
set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
