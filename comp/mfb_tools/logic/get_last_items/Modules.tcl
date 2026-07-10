# Modules.tcl: Components include script
# Copyright (C) 2026 CESNET z.s.p.o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set GEN_MUX_BASE "$OFM_PATH/comp/base/logic/mux"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [list "GEN_MUX" $GEN_MUX_BASE "FULL"]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/mfb_get_last_items.vhd"
