# Modules.tcl: Modules of the component
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause


# Set paths
set PKG_BASE       "$OFM_PATH/comp/base/pkg"
set BASE_BASE      "$OFM_PATH/comp/base"
set PPW_BASE       "$OFM_PATH/comp/pcie/pkt_writer"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"
lappend PACKAGES "$PKG_BASE/dma_bus_pack.vhd"

# Components
lappend COMPONENTS [ list "FIFOX_MULTI"    "$BASE_BASE/fifo/fifox_multi"  "FULL" ]
lappend COMPONENTS [ list "PPW_INSTR_GEN"  "$PPW_BASE/comp/instr_gen"     "FULL" ]

# Modules
lappend MOD "$ENTITY_BASE/ppr_dma_uphdr_gen.vhd"
lappend MOD "$ENTITY_BASE/ppr_request_processor.vhd"
