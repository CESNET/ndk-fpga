# Modules.tcl: Components include script
# Copyright (C) 2017 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set FIFO_BRAM_BASE "$OFM_PATH/comp/base/fifo/fifo_bram"

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set COMPONENTS [list \
   [list "fifo_bram" $FIFO_BRAM_BASE "behavioral" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mfb_fifo_bram.vhd"
