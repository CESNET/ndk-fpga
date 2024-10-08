# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE            "$OFM_PATH/comp/base/pkg"
set SDP_BRAM_BASE       "$OFM_PATH/comp/base/mem/sdp_bram"
set TDP_BRAM_BASE       "$OFM_PATH/comp/base/mem/dp_bram"
set BARREL_SHIFTER_BASE "$OFM_PATH/comp/base/logic/barrel_shifter"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

# Components
lappend COMPONENTS [ list "SDP_BRAM"            $SDP_BRAM_BASE          "FULL" ]
lappend COMPONENTS [ list "TDP_BRAM"            $TDP_BRAM_BASE          "FULL" ]
lappend COMPONENTS [ list "BARREL_SHIFTER_GEN"  $BARREL_SHIFTER_BASE    "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/tx_dma_pcie_trans_buffer.vhd"
