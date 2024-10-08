# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2012 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set ASFIFO_BASE 		"$OFM_PATH/comp/base/fifo/asfifo_bram_datamux/asfifo_mux_1to2"
set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"
# List of components
set COMPONENTS [list \
                [list "ASFIFO_MUX_1TO2"  $ASFIFO_BASE "FULL"]  \
                [list "ASFIFO_BRAM"  $ASFIFO_BASE "FULL"] \
                ]
set MOD "$MOD $ENTITY_BASE/dma_fifo_1to2_ent.vhd"
set MOD "$MOD $ENTITY_BASE/dma_fifo_1to2_arch.vhd"
