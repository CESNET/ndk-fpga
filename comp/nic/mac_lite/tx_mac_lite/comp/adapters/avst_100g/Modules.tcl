# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PKG_BASE           "$OFM_PATH/comp/base/pkg"

set FLU2FL_BASE    "$OFM_PATH/comp/flu_tools/fl/flu2fl"
set MFB_FIFOX_BASE "$OFM_PATH/comp/mfb_tools/storage/fifox"
set MFB_PIPE_BASE  "$OFM_PATH/comp/mfb_tools/flow/pipe"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"

set COMPONENTS [ list \
   [ list "FLU2FL"       $FLU2FL_BASE      "FULL"] \
   [ list "MFB_FIFOX"    $MFB_FIFOX_BASE   "FULL"] \
   [ list "MFB_PIPE"     $MFB_PIPE_BASE    "FULL"] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/avst_100g.vhd"
