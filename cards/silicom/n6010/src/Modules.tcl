# Modules.tcl: script to compile card
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Martin Matějka <xmatej55@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# converting input list to associative array
array set ARCHGRP_ARR $ARCHGRP

set PMCI_TOP_BASE "$ENTITY_BASE/comp/pmci"
set FPGA_COMMON_BASE "$ARCHGRP_ARR(CORE_BASE)/top"

lappend COMPONENTS [list "FPGA_COMMON"       $FPGA_COMMON_BASE       $ARCHGRP]
lappend COMPONENTS [list "PMCI_TOP"          $PMCI_TOP_BASE            "FULL"]

# IP components
set IP_COMMON_TCL $ARCHGRP_ARR(IP_TEMPLATE_ROOT)/common.tcl
source $IP_COMMON_TCL

set ARCHGRP_ARR(IP_COMMON_TCL)    $IP_COMMON_TCL
set ARCHGRP_ARR(IP_TEMPLATE_BASE) $ARCHGRP_ARR(IP_TEMPLATE_ROOT)/intel
set ARCHGRP_ARR(IP_MODIFY_BASE)   $ENTITY_BASE/ip
set ARCHGRP_ARR(IP_DEVICE_FAMILY) "Agilex"
set ARCHGRP_ARR(IP_DEVICE)        $ARCHGRP_ARR(FPGA)

set PCIE_CONF [dict create 0 "1x16" 1 "2x8"]
set PTILE_PCIE_IP_NAME "ptile_pcie_[dict get $PCIE_CONF $ARCHGRP_ARR(PCIE_ENDPOINT_MODE)]"

set ETH_CONF [dict create 100 "1x100g" 25 "4x25g" 10 "4x10g"]
set ETILE_ETH_IP_NAME "etile_eth_[dict get $ETH_CONF $ARCHGRP_ARR(ETH_PORT_SPEED,0)]"

# see '$ARCHGRP_ARR(CORE_BASE)/src/ip/common.tcl' for more information regarding the fields
#                         script_path    script_name       ip_comp_name     type  modify
lappend IP_COMPONENTS [list  "clk"    "iopll"            "iopll_ip"           0      1]
lappend IP_COMPONENTS [list  "mem"    "ddr4_calibration" "ddr4_calibration"   0      1]
lappend IP_COMPONENTS [list  "mem"    "onboard_ddr4"     "onboard_ddr4"       0      1]
lappend IP_COMPONENTS [list  "misc"   "mailbox_client"   "mailbox_client_ip"  0      0]
lappend IP_COMPONENTS [list  "misc"   "reset_release"    "reset_release_ip"   0      0]
lappend IP_COMPONENTS [list  "pcie"   "ptile_pcie"       $PTILE_PCIE_IP_NAME  0      1]

if {$ARCHGRP_ARR(NET_MOD_ARCH) eq "E_TILE"} {
    lappend IP_COMPONENTS [list "eth"   "etile_eth"      $ETILE_ETH_IP_NAME   0      1]
}

if {$ARCHGRP_ARR(VIRTUAL_DEBUG_ENABLE)} {
    lappend IP_COMPONENTS [list "misc"  "jtag_op"        "jtag_op_ip"         0      0]
}

lappend MOD {*}[get_ip_mod_files $IP_COMPONENTS [array get ARCHGRP_ARR]]

# Top-level
lappend MOD "$ENTITY_BASE/fpga.vhd"
