#
# Modules.tcl:
# Copyright (C) 2011 CESNET
# Author(s): Stepan Friedl <friedl@cesnet.cz>, Jakub Cabal <jakubcabal@gmail.com>
#
# SPDX-License-Identifier: BSD-3-Clause


set PCS_BASE           "$ENTITY_BASE/comp/pcs"
set PMA_BASE           "$ENTITY_BASE/comp/pma"
set MGMT_BASE          "$OFM_PATH/comp/nic/eth_phy/comp/mgmt"
set ASYNC_RESET_BASE   "$OFM_PATH/comp/base/async/reset/"
set OPEN_LOOP_BASE     "$OFM_PATH/comp/base/async/open_loop"
set BUS_HANDSHAKE_BASE "$OFM_PATH/comp/base/async/bus_handshake"

lappend COMPONENTS  [list "40GE_V7_PCS"         $PCS_BASE           "FULL"]
lappend COMPONENTS  [list "40GE_V7_PMA"         $PMA_BASE           "FULL"]
lappend COMPONENTS  [list "MGMT"                $MGMT_BASE          "FULL"]
lappend COMPONENTS  [list "ASYNC_RESET"         $ASYNC_RESET_BASE   "FULL"]
lappend COMPONENTS  [list "ASYNC_OPEN_LOOP"     $OPEN_LOOP_BASE     "FULL"]
lappend COMPONENTS  [list "ASYNC_BUS_HANDSHAKE" $BUS_HANDSHAKE_BASE "FULL"]

# Top level
lappend MOD "$ENTITY_BASE/40ge_phy_ent.vhd"
lappend MOD "$ENTITY_BASE/40ge_phy_arch.vhd"

if {$ARCHGRP == "SIM"} {
    lappend MOD "$ENTITY_BASE/comp/pma/gty_40ge_sim_netlist.vhdl"
    lappend MOD "/usr/local/fpga/Vivado/2021.1/data/verilog/src/glbl.v"
}

