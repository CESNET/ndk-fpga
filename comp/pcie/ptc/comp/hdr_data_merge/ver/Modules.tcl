# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set MFB_ASFIFO_BASE     "$OFM_PATH/comp/mfb_tools/storage/asfifox"
set SUM_ONE_BASE        "$OFM_PATH/comp/base/logic/sum_one"
set CODAPA_CHECKER_BASE "$ENTITY_BASE/../../codapa_checker"
set ASFIFO_BASE         "$OFM_PATH/comp/base/fifo/asfifo_bram"

set SV_MFB_BASE            "$OFM_PATH/comp/mfb_tools/ver"
set SV_MVB_BASE            "$OFM_PATH/comp/mvb_tools/ver"

set COMPONENTS [list \
   [ list "MFB_ASFIFOX"    $MFB_ASFIFO_BASE     "FULL"] \
   [ list "SUM_ONE"        $SUM_ONE_BASE        "FULL"] \
   [ list "CODAPA_CHECKER" $CODAPA_CHECKER_BASE "FULL"] \
   [ list "ASFIFO_BRAM"    $ASFIFO_BASE         "FULL"] \
   [ list "SV_MFB"         $SV_MFB_BASE         "FULL"] \
   [ list "SV_MVB"         $SV_MVB_BASE         "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/tbench/dut_wrapper.vhd"
set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
