# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2012 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set ASFIFO_BASE 		"$OFM_PATH/comp/base/fifo/asfifox"
set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"
# List of components
set COMPONENTS [list \
                [list "ASFIFO"  $ASFIFO_BASE "FULL"] \
                ]
set MOD "$MOD $ENTITY_BASE/dma_fifo_2to1_ent.vhd"
set MOD "$MOD $ENTITY_BASE/dma_fifo_2to1_arch.vhd"
