# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths
set PCIE_COMP_BASE    "$ENTITY_BASE/comp"
set MI_SPLITTER_BASE  "$OFM_PATH/comp/mi_tools/splitter_plus_gen"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/dma_bus_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/pcie_meta_pack.vhd"

# Components
lappend COMPONENTS [ list "PCIE_CORE"   "$PCIE_COMP_BASE/pcie_core" $ARCHGRP ]
lappend COMPONENTS [ list "PCIE_CTRL"   "$PCIE_COMP_BASE/pcie_ctrl" "FULL"   ]
lappend COMPONENTS [ list "MI_SPLITTER" $MI_SPLITTER_BASE           "FULL"   ]

# Files
lappend MOD "$ENTITY_BASE/pcie_top.vhd"

#lappend MOD "$ENTITY_BASE/DevTree.vhd"
#lappend MOD "$OFM_PATH/../cards/dk-dev-1sdx-p/src/ip/ptile_pcie_2x8.ip"
#lappend MOD "$OFM_PATH/../cards/dk-dev-1sdx-p/src/ip/ptile_pcie_1x16.ip"
