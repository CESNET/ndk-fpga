# Modules.tcl: Components include script
# Copyright (C) 2024 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Component paths

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
#lappend COMPONENTS [ list "ASFIFOX" "$OFM_PATH/comp/base/fifo/asfifox" "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/axis_splitter.vhd"
