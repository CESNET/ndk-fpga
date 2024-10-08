# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


# Paths to components
set HISTOGRAMER_BASE    "$OFM_PATH/comp/debug/histogramer"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "HISTOGRAMER"        $HISTOGRAMER_BASE       "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/data_logger.vhd"

# Component DevTree
lappend MOD "$ENTITY_BASE/DevTree.tcl"
