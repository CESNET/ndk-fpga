# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set SV_CRC_BASE       "$OFM_PATH/../modules/internal/base/ff/crc32"
set SV_MFB_BASE       "$OFM_PATH/comp/mfb_tools/ver"
set SV_MVB_BASE       "$OFM_PATH/comp/mvb_tools/ver"
set SV_MI32_BASE      "$OFM_PATH/comp/mi_tools/ver"
set SV_MII_TOOLS_BASE "$OFM_PATH/comp/nic/ver"
set SV_STATS_BASE     "$OFM_PATH/comp/proc/stat_unit/ver"

set MFB_FIFO_BASE     "$OFM_PATH/comp/mfb_tools/storage/fifo_bram"
set MVB_FIFO_BASE     "$OFM_PATH/comp/mvb_tools/storage/fifo"

set COMPONENTS [list \
   [ list "SV_CRC"              $SV_CRC_BASE        "ETHERNET"] \
   [ list "SV_MFB"              $SV_MFB_BASE        "FULL"] \
   [ list "SV_MVB"              $SV_MVB_BASE        "FULL"] \
   [ list "SV_MI32"             $SV_MI32_BASE       "FULL"] \
   [ list "SV_MII"              $SV_MII_TOOLS_BASE  "FULL"] \
   [ list "SV_STATS_TOOLS_BASE" $SV_STATS_BASE      "FULL"] \
   [ list "MFB_FIFO_BRAM"       $MFB_FIFO_BASE      "FULL"] \
   [ list "MVB_FIFO"            $MVB_FIFO_BASE      "FULL"] \
]

#set MOD "$MOD $ENTITY_BASE/tbench/fake_buffer.vhd"
set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
