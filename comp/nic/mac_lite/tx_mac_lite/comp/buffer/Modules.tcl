# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE           "$OFM_PATH/comp/base/pkg"
set ASFIFOX_BASE       "$OFM_PATH/comp/base/fifo/asfifox"
set MFB_PD_ASFIFO_BASE "$OFM_PATH/comp/mfb_tools/storage/pd_asfifo"
set MFB_FRAME_LNG_BASE "$OFM_PATH/comp/mfb_tools/logic/frame_lng"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
   [list "ASFIFOX"       $ASFIFOX_BASE       "FULL" ] \
   [list "MFB_PD_ASFIFO" $MFB_PD_ASFIFO_BASE "FULL" ] \
   [list "MFB_FRAME_LNG" $MFB_FRAME_LNG_BASE "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/buffer.vhd"
