# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "DMA_PACKAGE"     "$OFM_PATH/comp/base/pkg" "DMA_PKG" ]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/ptc_pcie_axi2mfb.vhd"
