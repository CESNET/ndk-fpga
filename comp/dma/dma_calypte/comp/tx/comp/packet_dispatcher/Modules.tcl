# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE        "$OFM_PATH/comp/base/pkg"
set FIFOX_BASE      "$OFM_PATH/comp/base/fifo/fifox"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"
lappend PACKAGES "$ENTITY_BASE/../../../rx/comp/hdr_manager/pkg/dma_hdr_pkg.vhd"

lappend COMPONENTS [ list "FIFOX"  $FIFOX_BASE    "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/tx_dma_pkt_dispatcher.vhd"
