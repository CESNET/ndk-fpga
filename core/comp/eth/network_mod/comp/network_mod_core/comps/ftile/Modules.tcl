# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Jakub Zahora <xzahor06@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set MGMT_BASE"$OFM_PATH/comp/nic/eth_phy/comp/mgmt"

# For local synthesis only !
#set ARCHGRP FB4CGG3

lappend COMPONENTS [list "MGMT" $MGMT_BASE "FULL"]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/ftile_init.vhd"
lappend MOD "$ENTITY_BASE/macseg_loop.vhd"
lappend MOD "$ENTITY_BASE/network_mod_core_ftile.vhd"
lappend MOD "$ENTITY_BASE/comps/bridge_drp/bridge_drp.vhd"



