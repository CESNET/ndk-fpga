# Modules.tcl: Local include tcl script
# Copyright (C) 2010 CESNET
# Author: Viktor Pus <pus@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

set MOD "$MOD $ENTITY_BASE/tag_sequencer.vhd"
set MOD "$MOD $ENTITY_BASE/tag_sequencer_top.vhd"


set DP_DISTMEM_BASE $OFM_PATH/comp/base/mem/gen_lutram/compatibility
set FIFO_BASE $OFM_PATH/comp/base/fifo/fifo

set COMPONENTS [list \
   [list "DP_DISTMEM" $DP_DISTMEM_BASE "FULL" ] \
   [list "FIFO"       $FIFO_BASE       "FULL" ] \
 ]
