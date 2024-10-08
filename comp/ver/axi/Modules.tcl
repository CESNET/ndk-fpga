# Modules.tcl: Local include Modules script
# Copyright (C) 2017 CESNET
# Author: Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

if { $ARCHGRP == "FULL" } {
  set MOD "$MOD $ENTITY_BASE/sv_axi_pkg.sv"
}

if { $ARCHGRP == "PCIE" } {
    lappend COMPONENTS [list "SV_AXI_PKG" $ENTITY_BASE "FULL"]
    set MOD "$MOD $ENTITY_BASE/sv_axi_pcie_pkg.sv"
}

if { $ARCHGRP == "MIROOT" } {
    lappend COMPONENTS [list "SV_AXI_PKG" $ENTITY_BASE "FULL"]
    set MOD "$MOD $ENTITY_BASE/sv_axi_completer_pkg.sv"
}
