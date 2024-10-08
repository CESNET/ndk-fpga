# Modules.tcl: Components include script
# Copyright (C) 2017 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set MFB_FIFO_BRAM_BASE "$OFM_PATH/comp/mfb_tools/storage/fifo_bram"
set GEN_MUX_BASE       "$OFM_PATH/comp/base/logic/mux"

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set COMPONENTS [list \
   [list "MFB_FIFO_BRAM" $MFB_FIFO_BRAM_BASE "behavioral" ] \
   [list "GEN_MUX"       $GEN_MUX_BASE       "FULL"       ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mfb_frame_recorder.vhd"
