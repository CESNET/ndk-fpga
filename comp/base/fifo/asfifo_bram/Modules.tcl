# Modules.tcl: Local include tcl script
# Copyright (C) 2014 CESNET
# Author: Martin Mikusek <martin.mikusek@liberouter.org>
#         Jakub Cabal    <jakubcabal@gmail.com>
#
# SPDX-License-Identifier: BSD-3-Clause
#

# Base directories
set DP_BMEM_BASE    "$OFM_PATH/comp/base/mem/dp_bmem"
set OPEN_LOOP_BASE  "$OFM_PATH/comp/base/async/open_loop_smd"
set ASYNC_HANDSHAKE_BASE "$OFM_PATH/comp/base/async/bus_handshake"

if { $ENTITY == "ASFIFO_BRAM" } {
   # Source files for implemented component
   if { $ARCHGRP == "FULL" } {

      # List of components
      set COMPONENTS [list \
                        [list "DP_BMEM"   $DP_BMEM_BASE  "FULL"]  \
                        [list "ASYNC_OPEN_LOOP_SMD"  $OPEN_LOOP_BASE "FULL"]  \
                     ]

      set MOD "$MOD $ENTITY_BASE/asfifo_bram.vhd"
   }
}

if { $ENTITY == "ASFIFO_BRAM_RELEASE" } {
   # Source files for implemented component
   if { $ARCHGRP == "FULL" } {

      # List of components
      set COMPONENTS [list \
                        [list "ASYNC_OPEN_LOOP_SMD"  $OPEN_LOOP_BASE "FULL"]  \
                        [list "ASYNC_HANDSHAKE" $ASYNC_HANDSHAKE_BASE "FULL"] \
                        [list "DP_BMEM"   $DP_BMEM_BASE  "FULL"]  \
                     ]

      set MOD "$MOD $ENTITY_BASE/asfifo_bram_release.vhd"
   }
}

if { $ENTITY == "ASFIFO_BRAM_BLOCK" } {
   # Source files for implemented component
   if { $ARCHGRP == "FULL" } {

      # List of components
      set COMPONENTS [list \
                        [list "ASYNC_OPEN_LOOP_SMD"  $OPEN_LOOP_BASE "FULL"]  \
                        [list "ASYNC_HANDSHAKE" $ASYNC_HANDSHAKE_BASE "FULL"] \
                        [list "DP_BMEM"   $DP_BMEM_BASE  "FULL"]  \
                     ]

      set MOD "$MOD $ENTITY_BASE/asfifo_bram_block.vhd"
   }
}
