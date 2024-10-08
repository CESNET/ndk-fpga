# Modules.tcl: Local include tcl script
# Copyright (C) 2016 CESNET
# Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MATH_PKG  "$OFM_PATH/comp/base/pkg"

set MOD "$MOD $ENTITY_BASE/fifo_pipe.vhd"
set FIFO_BASE "$OFM_PATH/comp/base/fifo/fifo"
set SH_FIFO_BASE "$OFM_PATH/comp/base/fifo/sh_fifo"

set COMPONENTS [ list \
                  [ list "FIFO"                 $FIFO_BASE                 "FULL" ] \
                  [ list "SH_FIFO"              $SH_FIFO_BASE              "FULL" ] \
               ]

set PACKAGES "$PACKAGES $MATH_PKG/math_pack.vhd"
