# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE           "$OFM_PATH/comp/base/pkg"
set MVB_SHAKEDOWN_BASE "$OFM_PATH/comp/mvb_tools/flow/shakedown"
set FIFOXM_BASE        "$OFM_PATH/comp/base/fifo/fifox_multi"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
   [list "MVB_SHAKEDOWN" $MVB_SHAKEDOWN_BASE "FULL" ] \
   [list "FIFOXM"        $FIFOXM_BASE        "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/crc_insert.vhd"
