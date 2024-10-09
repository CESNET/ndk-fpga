# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths
set MI_ASYNC_BASE    "$OFM_PATH/comp/mi_tools/async"
set MI_SPLITTER_BASE "$OFM_PATH/comp/mi_tools/splitter_plus_gen"


# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "MI_ASYNC"    $MI_ASYNC_BASE    "FULL" ]
lappend COMPONENTS [ list "MI_SPLITTER" $MI_SPLITTER_BASE "FULL" ]


# Files
lappend MOD "$ENTITY_BASE/boot_ctrl.vhd"
lappend MOD "$ENTITY_BASE/DevTree.tcl"
