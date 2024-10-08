# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PKG_BASE          "$OFM_PATH/comp/base/pkg"
set FIFOX_MULTI_BASE  "$OFM_PATH/comp/base/fifo/fifox_multi"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
   [list "FIFOX_MULTI"  $FIFOX_MULTI_BASE  "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mfb_user_packet_gen.vhd"
