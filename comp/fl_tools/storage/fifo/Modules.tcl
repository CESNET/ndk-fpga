# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Viktor Pus <pus@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

set FIFO_BASE        "$OFM_PATH/comp/base/fifo/fifo"
set MATH_PKG_BASE    "$OFM_PATH/comp/base/pkg"
set FIFO_BRAM_BASE   "$OFM_PATH/comp/base/fifo/fifo_bram"

# Entities
set MOD "$MOD $ENTITY_BASE/fifo_ent.vhd"
set MOD "$MOD $ENTITY_BASE/pfifo_ent.vhd"
set MOD "$MOD $ENTITY_BASE/fifo8_ent.vhd"
set MOD "$MOD $ENTITY_BASE/pfifo8_ent.vhd"
#set MOD "$MOD $ENTITY_BASE/dfifo_ent.vhd"

# Local FIFO package
set PACKAGES "$PACKAGES $ENTITY_BASE/fifo_pkg.vhd"
# Global FrameLink package
set PACKAGES "$PACKAGES $ENTITY_BASE/../../pkg/fl_pkg.vhd"

# Wrappers for normal FIFO
set MOD "$MOD $ENTITY_BASE/fifo_fl8.vhd"
set MOD "$MOD $ENTITY_BASE/fifo_fl16.vhd"
set MOD "$MOD $ENTITY_BASE/fifo_fl32.vhd"
set MOD "$MOD $ENTITY_BASE/fifo_fl64.vhd"
set MOD "$MOD $ENTITY_BASE/fifo_fl128.vhd"

# Wrappers for packet FIFO
set MOD "$MOD $ENTITY_BASE/pfifo_fl8.vhd"
set MOD "$MOD $ENTITY_BASE/pfifo_fl16.vhd"
set MOD "$MOD $ENTITY_BASE/pfifo_fl32.vhd"
set MOD "$MOD $ENTITY_BASE/pfifo_fl64.vhd"
set MOD "$MOD $ENTITY_BASE/pfifo_fl128.vhd"


if { $ARCHGRP == "FULL" } {
      # Common entities to compress / decompress (S|E)O(P|F) signals
      set MOD "$MOD $ENTITY_BASE/compress.vhd"
      set MOD "$MOD $ENTITY_BASE/decompress_any.vhd"

      set MOD "$MOD $ENTITY_BASE/decompress.vhd"
      # Deprecated

      # Full architectures
      set MOD "$MOD $ENTITY_BASE/fifo_arch_full.vhd"
      set MOD "$MOD $ENTITY_BASE/pfifo_arch_full.vhd"
      set MOD "$MOD $ENTITY_BASE/fifo8_arch_full.vhd"
      set MOD "$MOD $ENTITY_BASE/pfifo8_arch_full.vhd"
#      set MOD "$MOD $ENTITY_BASE/dfifo.vhd"

      # Subcomponents
      set COMPONENTS [list [list "FIFO_S"      $FIFO_BASE      "BEHAV"] \
                           [list "PKG" $MATH_PKG_BASE "MATH"] \
                           [list "FIFO_BRAM_S" $FIFO_BRAM_BASE "FULL"]]
   }

if { $ARCHGRP == "EMPTY" } {
      # Empty architectures
      set MOD "$MOD $ENTITY_BASE/fifo_arch_empty.vhd"
      set MOD "$MOD $ENTITY_BASE/pfifo_arch_empty.vhd"
      set MOD "$MOD $ENTITY_BASE/fifo8_arch_empty.vhd"
      set MOD "$MOD $ENTITY_BASE/pfifo8_arch_empty.vhd"

      set COMPONENTS [list \
                        [list "PKG" $MATH_PKG_BASE "MATH"] \
                     ]
   }
