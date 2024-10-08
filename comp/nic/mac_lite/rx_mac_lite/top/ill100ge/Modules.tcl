# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PKG_BASE          "$OFM_PATH/comp/base/pkg"
set AVST_ADAPTER_BASE "$OFM_PATH/comp/nic/mac_lite/rx_mac_lite/comp/adapters/avst_simple"
set RX_MAC_LITE_BASE  "$OFM_PATH/comp/nic/mac_lite/rx_mac_lite"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/eth_hdr_pack.vhd"

set COMPONENTS [list \
    [list "AVST_ADAPTER" $AVST_ADAPTER_BASE "FULL" ] \
    [list "RX_MAC_LITE"  $RX_MAC_LITE_BASE  "NO_CRC" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/rx_mac_lite_ill100ge.vhd"
