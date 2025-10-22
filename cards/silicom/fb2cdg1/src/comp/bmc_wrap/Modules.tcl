# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend MOD "$ENTITY_BASE/bmc_wrap_ent.vhd"

if {$ARCHGRP == "EMPTY"} {
    lappend MOD "$ENTITY_BASE/bmc_wrap_empty.vhd"
} else {
    # Paths
    set PMCI_FB2CDG1_BASE "$OFM_PATH/extra/ip-3rdparty/silicom/fb2cdg1"

    if ![file exists $PMCI_FB2CDG1_BASE/Modules.tcl] {
        puts "-----------------------------------------------------------------------------"
        puts "ERROR: BMC IP source codes are missing!"
        puts "-----------------------------------------------------------------------------"
        puts "Try using make parameter BMC_ENABLE=0 or get the necessary source codes."
        puts "You can contact an NDK partner for help (see partner list in top-level README.md)."
        puts "-----------------------------------------------------------------------------"
        exit 1
    }

    # Components
    lappend COMPONENTS [ list "PMCI_FB2CDG1" $PMCI_FB2CDG1_BASE "FULL"]

    # Files
    lappend MOD "$ENTITY_BASE/bmc_wrap.vhd"
}
