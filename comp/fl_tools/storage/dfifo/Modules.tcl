# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2009 CESNET
# Author: Jiri Novotnak <xnovot87@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set FIFO_BASE        "$OFM_PATH/comp/base/fifo/fifo"
set MATH_PKG_BASE    "$OFM_PATH/comp/base/pkg"
set FIFO_BRAM_BASE   "$OFM_PATH/comp/base/fifo/fifo_bram"
set COMPRESS_BASE    "$OFM_PATH/comp/fl_tools/storage/fifo"
set SDP_BMEM_BASE    "$OFM_PATH/comp/base/mem/dp_bmem"

# Entities
set MOD "$MOD $ENTITY_BASE/dfifo_ent.vhd"
#set MOD "$MOD $OFM_PATH/comp/fl_tools/storage/dfifo/dfifo_ent.vhd"

# Global FrameLink package
set PACKAGES "$PACKAGES $ENTITY_BASE/../../pkg/fl_pkg.vhd"

if { $ARCHGRP == "FULL" } {
      # Common entities to compress / decompress (S|E)O(P|F) signals
      set MOD "$MOD $COMPRESS_BASE/compress.vhd"
      set MOD "$MOD $COMPRESS_BASE/decompress_any.vhd"

      set MOD "$MOD $COMPRESS_BASE/decompress.vhd"
      # Deprecated

      # Full architectures
      set MOD "$MOD $ENTITY_BASE/dfifo.vhd"

      # Subcomponents
      set COMPONENTS [list [list "FIFO_S"      $FIFO_BASE      "BEHAV"] \
                           [list "PKG" $MATH_PKG_BASE "MATH"] ]
   }

if { $ARCHGRP == "BRAM" } {
      # Common entities to compress / decompress (S|E)O(P|F) signals
      set MOD "$MOD $COMPRESS_BASE/compress.vhd"
      set MOD "$MOD $COMPRESS_BASE/decompress_any.vhd"

      set MOD "$MOD $COMPRESS_BASE/decompress.vhd"
      # Deprecated

      # Full architectures
      set MOD "$MOD $ENTITY_BASE/dfifo_bram.vhd"

      # Subcomponents
      set COMPONENTS [list [list "FIFO_S"      $FIFO_BASE      "BEHAV"] \
                           [list "SDP_BMEM"    $SDP_BMEM_BASE  "FULL"]  \
                           [list "PKG" $MATH_PKG_BASE "MATH"] ]
   }
