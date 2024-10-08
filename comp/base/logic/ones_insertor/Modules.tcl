# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


# Set paths
set PKG_BASE     "$OFM_PATH/comp/base/pkg"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

# Source files for implemented component
lappend MOD "$ENTITY_BASE/ones_insertor.vhd"
