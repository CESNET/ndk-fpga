# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal   <cabal@cesnet.cz>
#            Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set ADAPTER_SHAKEDOWN_BASE  "$OFM_PATH/comp/nic/mac_lite/rx_mac_lite/comp/adapters/eth_avst/eth_avst_adapter_shakedown"
set PKG_BASE                "$OFM_PATH/comp/base/pkg"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
    [ list "ETH_AVST_ADAPTER_SHAKEDOWN"   $ADAPTER_SHAKEDOWN_BASE   "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/eth_avst_adapter.vhd"
