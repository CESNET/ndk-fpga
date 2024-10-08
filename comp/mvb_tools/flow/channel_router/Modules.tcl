# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE "$OFM_PATH/comp/base/pkg"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

# Source files for implemented component
lappend MOD "$ENTITY_BASE/mvb_channel_router.vhd"
lappend MOD "$ENTITY_BASE/mvb_channel_router_mi.vhd"
lappend MOD "$ENTITY_BASE/DevTree.tcl"
