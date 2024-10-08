# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2014 CESNET
# Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

if { $ARCHGRP == "COMMANDS" } {
   set MOD "$MOD $ENTITY_BASE/flu_adapter_pkg.vhd"
}
