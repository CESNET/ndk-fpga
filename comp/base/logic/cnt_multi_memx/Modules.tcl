# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jan Kubalek <kubalek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE      "$OFM_PATH/comp/base/pkg"
set MEMX_BASE     "$OFM_PATH/comp/base/mem/sdp_memx"
set FIFOX_BASE    "$OFM_PATH/comp/base/fifo/fifox"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
    [ list "FIFOX"            "$FIFOX_BASE"                      "FULL" ] \
    [ list "MEMX"             "$MEMX_BASE"                       "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/cnt_multi_memx.vhd"
