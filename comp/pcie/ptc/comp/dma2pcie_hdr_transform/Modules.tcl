# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET z. s. p. o.
# Author: Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE            "$OFM_PATH/comp/base/pkg"

lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"
lappend PACKAGES "$PKG_BASE/dma_bus_pack.vhd"

# list of sub-components
lappend COMPONENTS [ list "PCIE_HDR_GEN"         "$OFM_PATH/comp/pcie/others/hdr_gen"            "FULL" ]

# entity and architecture
lappend MOD "$ENTITY_BASE/ptc_dma2pcie_hdr_transform_ent.vhd"
lappend MOD "$ENTITY_BASE/ptc_dma2pcie_hdr_transform_full.vhd"
