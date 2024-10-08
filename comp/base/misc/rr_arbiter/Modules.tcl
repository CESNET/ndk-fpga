# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
#         Patrik Beck <beck@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components


if { $ARCHGRP == "FULL" } {
  set COMMON_BASE    "$ENTITY_BASE/../"

  set MOD "$MOD $ENTITY_BASE/rr_arbiter_unit.vhd"
  set MOD "$MOD $ENTITY_BASE/rr_arbiter.vhd"

}
