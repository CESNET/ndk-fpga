# Modules.tcl: Modules.tcl script
# Copyright (C) 2014 CESNET
# Author(s): Jakub Cabal <jakubcabal@gmail.com>
#
# SPDX-License-Identifier: BSD-3-Clause


set ASFIFO_BASE "$OFM_PATH/comp/base/fifo/asfifo"

set COMPONENTS [ list \
  [ list "ASFIFO" $ASFIFO_BASE "FULL" ] \
  ]

set MOD "$MOD $ENTITY_BASE/dma_asfifo_lut.vhd"
