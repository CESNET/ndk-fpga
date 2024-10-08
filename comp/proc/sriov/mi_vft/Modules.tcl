# Modules.tcl: Local include tcl script
# Copyright (C) 2010 CESNET
# Author(s): Vaclav Bartos <washek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

set MOD "$MOD $ENTITY_BASE/mi_vft.vhd"

if { $ARCHGRP == "EMPTY" } {
  set MOD "$MOD $ENTITY_BASE/mi_vft_empty.vhd"
}

if { $ARCHGRP == "NIC" } {
  set MOD "$MOD $ENTITY_BASE/mi_vft_nic.vhd"
}

if {$ARCHGRP == "NIC_USP"} {
    set MOD "$MOD $ENTITY_BASE/mi_vft_nic_usp.vhd"
}
