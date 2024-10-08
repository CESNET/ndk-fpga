# Modules.tcl: Modules.tcl script
# Copyright (C) 2014 CESNET
# Author(s): Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set ASFIFO_BASE "$OFM_PATH/comp/base/fifo/asfifo_bram_xilinx"

set COMPONENTS [ list \
  [ list "ASFIFO" $ASFIFO_BASE "FULL" ] \
  ]

set MOD "$MOD $ENTITY_BASE/asfifo_dma_bus_ent.vhd"
set MOD "$MOD $ENTITY_BASE/asfifo_dma_bus.vhd"
