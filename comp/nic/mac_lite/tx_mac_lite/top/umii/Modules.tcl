# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PKG_BASE         "$OFM_PATH/comp/base/pkg"
set UMII_ENC_BASE    "$OFM_PATH/comp/nic/mac_lite/tx_mac_lite/comp/adapters/umii_enc"
set TX_MAC_LITE_BASE "$OFM_PATH/comp/nic/mac_lite/tx_mac_lite"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
    [list "UMII_ENC"    $UMII_ENC_BASE    "FULL" ] \
    [list "TX_MAC_LITE" $TX_MAC_LITE_BASE "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/tx_mac_lite_umii.vhd"
