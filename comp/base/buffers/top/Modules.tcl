# Modules.tcl: Local include tcl script
# Copyright (C) 2008 CESNET
# Author: Vozenilek Jan <xvozen00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#

# Base directories
set MATH_PACK_BASE "$OFM_PATH/comp/base/pkg"

if { $ARCHGRP == "FULL" } {
    set BUFCOMP_BASE  "$OFM_PATH/comp/base/buffers/comp"
    set BMEM_BASE     "$OFM_PATH/comp/base/mem/dp_bmem"
    set SH_FIFO_BASE  "$OFM_PATH/comp/base/fifo/sh_fifo"

    lappend PACKAGES  "$MATH_PACK_BASE/math_pack.vhd"

    set COMPONENTS [list \
        [list "MATH_PACK"  $MATH_PACK_BASE "MATH"] \
        [list "RX_SWITCH"  $BUFCOMP_BASE   "FULL"] \
        [list "TX_SWITCH"  $BUFCOMP_BASE   "FULL"] \
        [list "BUF_MEM"    $BUFCOMP_BASE   "FULL"] \
        [list "BUF_STATUS" $BUFCOMP_BASE   "FULL"] \
        [list "BUF_STATUS_ALMOST_FULL" $BUFCOMP_BASE   "FULL"] \
        [list "SH_FIFO"    $SH_FIFO_BASE   "FULL"]]

    lappend MOD "$ENTITY_BASE/nfifo2mem.vhd"
    lappend MOD "$ENTITY_BASE/nfifo.vhd"
    lappend MOD "$ENTITY_BASE/nfifo2fifo.vhd"
    lappend MOD "$ENTITY_BASE/mem2nfifo.vhd"
    lappend MOD "$ENTITY_BASE/fifo2nfifo.vhd"
    lappend MOD "$ENTITY_BASE/mfifo2mem.vhd"
    lappend MOD "$ENTITY_BASE/mfifo2mem_almost_full.vhd"
}
