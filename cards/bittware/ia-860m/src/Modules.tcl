# Modules.tcl: script to compile Bittware IA-860m card FPGA design
# Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
# Author(s): Denis Kurka <kurka@dyna-nic.com>,
#
# SPDX-License-Identifier: BSD-3-Clause

# converting input list to associative array
array set ARCHGRP_ARR $ARCHGRP

# Paths
set FPGA_COMMON_BASE  "$ARCHGRP_ARR(CORE_BASE)/top"

# Components
lappend COMPONENTS [list "FPGA_COMMON" $FPGA_COMMON_BASE $ARCHGRP]
lappend COMPONENTS [list "BMC_WARP" "$ENTITY_BASE/comp/bmc_wrap" $ARCHGRP_ARR(BMC_CTRL_ARCH)]

# IP components
set IP_COMMON_TCL $ARCHGRP_ARR(IP_TEMPLATE_ROOT)/common.tcl
source $IP_COMMON_TCL

set ARCHGRP_ARR(IP_COMMON_TCL)    $IP_COMMON_TCL
set ARCHGRP_ARR(IP_TEMPLATE_BASE) $ARCHGRP_ARR(IP_TEMPLATE_ROOT)/intel
set ARCHGRP_ARR(IP_MODIFY_BASE)   $ENTITY_BASE/ip
set ARCHGRP_ARR(IP_DEVICE_FAMILY) "Agilex"
set ARCHGRP_ARR(IP_DEVICE)        $ARCHGRP_ARR(FPGA)

set PCIE_CONF [dict create 0 "1x16" 1 "2x8"]
set RTILE_PCIE_IP_NAME "rtile_pcie_gen$ARCHGRP_ARR(PCIE_GEN)_[dict get $PCIE_CONF $ARCHGRP_ARR(PCIE_ENDPOINT_MODE)]"

set ETH_CONF [dict create 400 "1x400g" ]
set FTILE_ETH_IP_NAME "ftile_eth_[dict get $ETH_CONF $ARCHGRP_ARR(ETH_PORT_SPEED,0)]"

# see '$ARCHGRP_ARR(CORE_BASE)/src/ip/common.tcl' for more information regarding the fields
#                         script_path     script_name        ip_comp_name       type  modify
lappend IP_COMPONENTS [list  "clk"     "ftile_pll"         "ftile_pll"            0      1]
lappend IP_COMPONENTS [list  "misc"    "mailbox_client"    "mailbox_client_ip"    0      0]
lappend IP_COMPONENTS [list  "clk"     "iopll"             "iopll_ip"             0      1]
lappend IP_COMPONENTS [list  "misc"    "reset_release"     "reset_release_ip"     0      0]
lappend IP_COMPONENTS [list  "pcie"    "rtile_pcie"        $RTILE_PCIE_IP_NAME    0      1]
lappend IP_COMPONENTS [list  "eth"     "ftile_eth"         $FTILE_ETH_IP_NAME     0      1]

if {$ARCHGRP_ARR(VIRTUAL_DEBUG_ENABLE)} {
    lappend IP_COMPONENTS [list "misc"  "jtag_op"          "jtag_op_ip"           0      0]
}

lappend MOD {*}[get_ip_mod_files $IP_COMPONENTS [array get ARCHGRP_ARR]]

# Top-level
if {$ARCHGRP_ARR(ETH_PORTS) == 3} {
    lappend MOD "$ENTITY_BASE/fpga_3ports.vhd"
} elseif {$ARCHGRP_ARR(ETH_PORTS) == 2} {
    lappend MOD "$ENTITY_BASE/fpga_2ports.vhd"
} else {
    error "Unsupported ETH_PORTS=$ARCHGRP_ARR(ETH_PORTS)! Supported values are 2 and 3."
}

