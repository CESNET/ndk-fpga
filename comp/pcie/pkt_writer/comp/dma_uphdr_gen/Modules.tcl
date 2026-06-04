# Modules.tcl: Modules of the component
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause


# Set paths
set PKG_BASE   "$OFM_PATH/comp/base/pkg"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

# Components
lappend COMPONENTS [ list "DMA_PACKAGE"     "$OFM_PATH/comp/base/pkg" "DMA_PKG" ]

# Modules
lappend MOD "$ENTITY_BASE/ppw_dma_uphdr_gen.vhd"
