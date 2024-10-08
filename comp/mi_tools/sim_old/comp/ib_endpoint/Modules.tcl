# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

if { $ARCHGRP == "FULL" } {

 set COMPONENTS [list \
     [list "FIFO_BRAM"    $OFM_PATH/comp/base/fifo/fifo_bram  "FULL"] \
     [list "SH_FIFO"      $OFM_PATH/comp/base/fifo/sh_fifo    "FULL"] \
     [list "TAG_SEQUENCER" $ENTITY_BASE/tag_sequencer     "FULL"] \
  ]

  set MOD "$MOD $ENTITY_BASE/../ib_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_upstream_priority_dec.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_downstream_buffer.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_shift_reg.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_be.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_write_fsm.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_read_shr.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_read_align.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_write_align.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_read_fsm.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_upstream_fsm_slave.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_upstream_fsm_master.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_hdr_gen_slave.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_hdr_gen_master.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_master_fsm.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_op_done_buffer.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_core.vhd"
  set MOD "$MOD $ENTITY_BASE/ib_endpoint_core_arch.vhd"
}
