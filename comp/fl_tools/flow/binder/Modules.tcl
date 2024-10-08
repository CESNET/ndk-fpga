# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2009 CESNET
# Author: Martin Kosek <kosek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set FL_BASE          "$ENTITY_BASE/../.."
set FIFO_BASE        "$FL_BASE/storage/fifo"
set PIPE_BASE        "$FL_BASE/flow/pipe"
set TRANSFORMER_BASE "$FL_BASE/flow/transformer"


set MOD "$MOD $ENTITY_BASE/binder_decl.vhd"
set MOD "$MOD $ENTITY_BASE/binder_ent.vhd"
set MOD "$MOD $FL_BASE/pkg/fl_pkg.vhd"

# Full FrameLink Binder
if { $ARCHGRP == "FULL" } {
   # NFIFO2FIFO Binder
   set MOD "$MOD $ENTITY_BASE/comp/frame_counter.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/frame_counters.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/rem_cmp.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/extrem_select.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/output_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/output.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/output_robin.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/output_framed.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/crossbar.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/align_frame_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/align_frame.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/data_transformer.vhd"
   set MOD "$MOD $ENTITY_BASE/binder_nfifo2fifo.vhd"

   # Simple Binder
   set MOD "$MOD $ENTITY_BASE/binder_simple.vhd"

   # Stupid Binder
   set MOD "$MOD $ENTITY_BASE/binder_stupid.vhd"

   # top level entity
   set MOD "$MOD $ENTITY_BASE/binder.vhd"


   # components
   set COMPONENTS [list \
      [ list "PKG_MATH"          $OFM_PATH/comp/base/pkg           "MATH"] \
      [ list "MUX"               $OFM_PATH/comp/base/logic/mux     "FULL"] \
      [ list "DEMUX"             $OFM_PATH/comp/base/logic/demux   "FULL"] \
      [ list "ENC"               $OFM_PATH/comp/base/logic/enc     "FULL"] \
      [ list "DEC1FN"            $OFM_PATH/comp/base/logic/dec1fn  "FULL"] \
      [ list "FL_FIFO"           $FIFO_BASE                    "FULL"] \
      [ list "FL_PIPE"           $PIPE_BASE                    "FULL"] \
      [ list "FL_TRANSFORMER"    $TRANSFORMER_BASE             "FULL"] \
      [ list "NFIFO2FIFO"        $OFM_PATH/comp/base/buffers/top   "FULL"] \
   ]
}

# Empty FrameLink Binder
if { $ARCHGRP == "EMPTY" } {
   set MOD "$MOD $ENTITY_BASE/binder_empty.vhd"
}

set MOD "$MOD $ENTITY_BASE/top/binder_fl16x4to64.vhd"
set MOD "$MOD $ENTITY_BASE/top/binder_fl16x2to16.vhd"
set MOD "$MOD $ENTITY_BASE/top/binder_fl16x2to64.vhd"
set MOD "$MOD $ENTITY_BASE/top/binder_fl32x2to32.vhd"
set MOD "$MOD $ENTITY_BASE/top/binder_fl32x4to32.vhd"
set MOD "$MOD $ENTITY_BASE/top/binder_fl32x4to64.vhd"

set MOD "$MOD $ENTITY_BASE/top/binder_x3_norec.vhd"
