# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE "$OFM_PATH/comp/base/pkg"
set MFB_BASE "$OFM_PATH/comp/mfb_tools"

lappend PACKAGES \
    "$PKG_BASE/math_pack.vhd" \
    "$PKG_BASE/type_pack.vhd" \

lappend COMPONENTS \
    [list "MFB_TO_LBUS_RECONF"          "$ENTITY_BASE/reconf"                                       "FULL"] \
    [list "MFB_AUXILIARY_SIGNALS"       "$MFB_BASE/logic/auxiliary_signals"                         "FULL"] \

# Source files for implemented component
lappend MOD \
    "$ENTITY_BASE/tx_lbus.vhd" \
