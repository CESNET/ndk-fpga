# Modules.tcl: Modules of the component
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause


# Set paths
set PKG_BASE            "$OFM_PATH/comp/base/pkg"
set MFB_STORAGE_BASE    "$OFM_PATH/comp/mfb_tools/storage"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"
lappend PACKAGES "$PKG_BASE/dma_bus_pack.vhd"

# Components
lappend COMPONENTS [ list "MFB_FIFOX"           "$MFB_STORAGE_BASE/fifox"          "FULL" ]
lappend COMPONENTS [ list "PPW_INSTR_GEN"       "$ENTITY_BASE/comp/instr_gen"      "FULL" ]
lappend COMPONENTS [ list "PPW_PKT_BREAKER"     "$ENTITY_BASE/comp/pkt_breaker"    "FULL" ]
lappend COMPONENTS [ list "PPW_DMA_UPHDR_GEN"   "$ENTITY_BASE/comp/dma_uphdr_gen"  "FULL" ]

# Modules
lappend MOD "$ENTITY_BASE/pcie_pkt_writer.vhd"
