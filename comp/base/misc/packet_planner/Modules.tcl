# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jan Kubalek <kubalek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE            "$OFM_PATH/comp/base/pkg"
set SUBCOMP_BASE        "$ENTITY_BASE/comp"
set FIFOXM_BASE         "$OFM_PATH/comp/base/fifo/fifox_multi"
set FIFOX_BASE          "$OFM_PATH/comp/base/fifo/fifox"
set DIC_BASE            "$OFM_PATH/comp/base/misc/deficit_idle_counter"
set SHAKEDOWN_BASE      "$OFM_PATH/comp/mvb_tools/flow/shakedown"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/dma_bus_pack.vhd"

#set FIFOX_BASE       "$OFM_PATH/comp/base/fifo/fifox"

set COMPONENTS [list \
    [ list "FIFOX_MULTI"      "$FIFOXM_BASE"                        "FULL" ] \
    [ list "FIFOX"            "$FIFOX_BASE"                         "FULL" ] \
    [ list "DIC"              "$DIC_BASE"                           "FULL" ] \
    [ list "SHAKEDOWN"        "$SHAKEDOWN_BASE"                     "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/packet_planner.vhd"
