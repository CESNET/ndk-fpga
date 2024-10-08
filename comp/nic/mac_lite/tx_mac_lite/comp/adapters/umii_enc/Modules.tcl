# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE     "$OFM_PATH/comp/base/pkg"
set BIN2HOT_BASE "$OFM_PATH/comp/base/logic/bin2hot"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
   [list "BIN2HOT" "$BIN2HOT_BASE" "FULL"] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/umii_enc.vhd"
