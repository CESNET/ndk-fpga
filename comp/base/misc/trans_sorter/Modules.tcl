# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE     "$OFM_PATH/comp/base/pkg"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
    [ list "FIFOX_MULTI"       "$OFM_PATH/comp/base/fifo/fifox_multi"       "FULL" ] \
]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/trans_sorter.vhd"
