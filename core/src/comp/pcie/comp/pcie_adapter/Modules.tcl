# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths
set PCIE_CONV_BASE "$OFM_PATH/comp/pcie/convertors"
set PCIE_CBLK_BASE "$OFM_PATH/comp/pcie/others/connection_block"
set PTC_COMP_BASE  "$OFM_PATH/comp/pcie/ptc/comp"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/pcie_meta_pack.vhd"

# Components
lappend COMPONENTS [ list "CONN_BLOCK" $PCIE_CBLK_BASE               "FULL" ]
lappend COMPONENTS [ list "CQ_AXI2MFB" "$PCIE_CONV_BASE/cq_axi2mfb"  "FULL" ]
lappend COMPONENTS [ list "CC_MFB2AXI" "$PCIE_CONV_BASE/cc_mfb2axi"  "FULL" ]
lappend COMPONENTS [ list "RC_AXI2MFB" "$PTC_COMP_BASE/pcie_axi2mfb" "FULL" ]
lappend COMPONENTS [ list "RQ_MFB2AXI" "$PTC_COMP_BASE/mfb2pcie_axi" "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/pcie_adapter.vhd"
