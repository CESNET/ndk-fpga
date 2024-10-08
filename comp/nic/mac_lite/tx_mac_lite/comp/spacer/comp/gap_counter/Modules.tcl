# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE           "$OFM_PATH/comp/base/pkg"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set DIC_BASE    "$COMP_BASE/400g/scheduler_tx/comp/scheduler_ctrl/comp/merger/comp/dic"

set COMPONENTS [list \
    [list "DIC"      $DIC_BASE     "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/gap_counter.vhd"
