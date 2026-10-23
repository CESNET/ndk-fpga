# Modules.tcl: Components include script
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2025
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE  "$OFM_PATH/comp/base/pkg"
set MFB_BASE  "$OFM_PATH/comp/mfb_tools"
set LBUS_BASE "$OFM_PATH/comp/nic/mac_lite/tx_mac_lite/comp/adapters/lbus"

lappend PACKAGES \
    "$PKG_BASE/math_pack.vhd" \
    "$PKG_BASE/type_pack.vhd" \

lappend COMPONENTS \
    [list "MFB_TO_LBUS_RECONF"          "$LBUS_BASE/reconf"                                       "FULL"] \
    [list "MFB_AUXILIARY_SIGNALS"       "$MFB_BASE/logic/auxiliary_signals"                       "FULL"] \

# Source files for implemented component
lappend MOD "$ENTITY_BASE/tx_saxis.vhd"
