# Modules.tcl: Components include script
# Copyright (C) 2024 CESNET
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE "$OFM_PATH/comp/base/pkg"

# Set packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/sp_rom_behav.vhd"
