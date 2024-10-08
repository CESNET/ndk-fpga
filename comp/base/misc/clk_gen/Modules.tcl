# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2012 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components
if { $ARCHGRP != "VIRTEX6" } {
    set MOD "$MOD $ENTITY_BASE/clk2x.vhd"
    set MOD "$MOD $ENTITY_BASE/clk4x.vhd"
    set MOD "$MOD $ENTITY_BASE/clk_gen.vhd"
    set PACKAGES "$PACKAGES $ENTITY_BASE/clk_gen_pkg.vhd"
}
