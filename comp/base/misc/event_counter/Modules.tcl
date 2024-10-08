# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jan Kubalek <kubalek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE            "$OFM_PATH/comp/base/pkg"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set FIFOX_BASE       "$OFM_PATH/comp/base/fifo/fifox"

set COMPONENTS [list \
    [ list "FIFOX"            "$FIFOX_BASE"                         "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/event_counter.vhd"
set MOD "$MOD $ENTITY_BASE/event_counter_mi_wrapper.vhd"
set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
