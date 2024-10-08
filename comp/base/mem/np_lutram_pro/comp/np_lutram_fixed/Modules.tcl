# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE  "$OFM_PATH/comp/base/pkg"

set GEN_LUTRAM_BASE "$OFM_PATH/comp/base/mem/gen_lutram"
set GEN_MUX_BASE    "$OFM_PATH/comp/base/logic/mux"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [ list \
    [ list "GEN_LUTRAM" $GEN_LUTRAM_BASE "FULL" ] \
    [ list "GEN_MUX"    $GEN_MUX_BASE    "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/np_lutram_fixed.vhd"
