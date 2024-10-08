# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Martinek Tomas <martinek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components
if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/cnt_types.vhd"
   set MOD "$MOD $ENTITY_BASE/cnt.vhd"
}
