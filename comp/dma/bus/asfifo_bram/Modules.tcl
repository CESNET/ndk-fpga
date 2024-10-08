# Modules.tcl: Modules.tcl script
# Copyright (C) 2014 CESNET
# Author(s): Jakub Cabal <jakubcabal@gmail.com>
#
# SPDX-License-Identifier: BSD-3-Clause


set MATH_PKG  "$OFM_PATH/comp/base/pkg"

set PACKAGES "$PACKAGES $MATH_PKG/math_pack.vhd"
set PACKAGES "$PACKAGES $MATH_PKG/type_pack.vhd"

set ASFIFO_BASE "$OFM_PATH/comp/base/fifo/asfifo_bram"

set COMPONENTS [ list \
  [ list "ASFIFO_BRAM" $ASFIFO_BASE "FULL" ] \
  ]

set MOD "$MOD $ENTITY_BASE/dma_asfifo_bram.vhd"
