# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

if { $ARCHGRP == "FULL" } {
  set MOD "$MOD $ENTITY_BASE/dpi_scoreboard_pkg.sv"
  set SV_LIB "$SV_LIB $ENTITY_BASE/dpi_scoreboard_pkg"
}
