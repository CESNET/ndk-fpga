# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PKG_BASE            "$OFM_PATH/comp/base/pkg"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/sum_one.vhd"
