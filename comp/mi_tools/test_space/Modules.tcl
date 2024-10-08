# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

# Source files for implemented component
lappend MOD "$ENTITY_BASE/mi_test_space.vhd"
lappend MOD "$ENTITY_BASE/DevTree.tcl"
