# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend MOD "$ENTITY_BASE/clk_gen_ent.vhd"

# Source files for implemented component
if {$ARCHGRP == "INTEL"} {
    lappend MOD "$ENTITY_BASE/clk_gen_intel.vhd"
    # IPs (PLL and Reset Release) must be loaded in top-level Modules.tcl
} elseif {$ARCHGRP == "USP"} {
    lappend MOD "$ENTITY_BASE/clk_gen_usp.vhd"
}
