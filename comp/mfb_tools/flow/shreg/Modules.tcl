# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE    "$OFM_PATH/comp/base/pkg"
set SH_REG_BASE "$OFM_PATH/comp/base/shreg/sh_reg_base"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"

set COMPONENTS [list \
   [list "SH_REG_BASE_STATIC" $SH_REG_BASE "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/shreg.vhd"
