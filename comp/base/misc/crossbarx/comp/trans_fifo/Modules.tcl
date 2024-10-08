# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE           "$OFM_PATH/comp/base/pkg"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set FIFOX_BASE    "$OFM_PATH/comp/base/fifo/fifox"

set COMPONENTS [list \
    [list "FIFOX"      $FIFOX_BASE     "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/trans_fifo.vhd"
