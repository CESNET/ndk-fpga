# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set MI_SPLITTER_BASE          "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set TX_MAC_LITE_BASE          "$OFM_PATH/comp/nic/mac_lite/tx_mac_lite"
set RX_MAC_LITE_BASE          "$OFM_PATH/comp/nic/mac_lite/rx_mac_lite"
set MFB_MERGER_BASE           "$OFM_PATH/comp/mfb_tools/flow/merger"
set MFB_SPLITTER_BASE         "$OFM_PATH/comp/mfb_tools/flow/splitter_simple"

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/eth_hdr_pack.vhd"

set COMPONENTS [concat $COMPONENTS [list \
    [ list "MI_SPLITTER_PLUS_GEN" $MI_SPLITTER_BASE          "FULL"   ] \
    [ list "TX_MAC_LITE"          $TX_MAC_LITE_BASE          "NO_CRC" ] \
    [ list "RX_MAC_LITE"          $RX_MAC_LITE_BASE          "NO_CRC" ] \
    [ list "MFB_MERGER_GEN"       $MFB_MERGER_BASE           "FULL"   ] \
    [ list "MFB_SPLIT_SIMPLE_GEN" $MFB_SPLITTER_BASE         "FULL"   ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/network_mod_logic.vhd"
# set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
