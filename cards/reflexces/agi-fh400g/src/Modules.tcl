# Modules.tcl: script to compile XpressSX AGI-FH400G
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>,
#            Jakub Záhora <zahora@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# converting input list to associative array
array set ARCHGRP_ARR $ARCHGRP

# Paths
set BOOT_CTRL_BASE "$OFM_PATH/../core/intel/src/comp/boot_ctrl"

# Components
lappend COMPONENTS [list "FPGA_COMMON" $ARCHGRP_ARR(CORE_BASE)  $ARCHGRP]
lappend COMPONENTS [list "BOOT_CTRL"   $BOOT_CTRL_BASE          "FULL"]

# IP components
source $ARCHGRP_ARR(CORE_BASE)/src/ip/common.tcl

set ARCHGRP_ARR(IP_TEMPLATE_BASE) $ARCHGRP_ARR(CORE_BASE)/src/ip/intel
set ARCHGRP_ARR(IP_MODIFY_BASE)   $ENTITY_BASE/ip
set ARCHGRP_ARR(IP_DEVICE_FAMILY) "Agilex"
set ARCHGRP_ARR(IP_DEVICE)        $ARCHGRP_ARR(FPGA)

set PCIE_CONF [dict create 0 "1x16" 1 "2x8"]
set RTILE_PCIE_IP_NAME "rtile_pcie_[dict get $PCIE_CONF $ARCHGRP_ARR(PCIE_ENDPOINT_MODE)]"

set ETH_CONF [dict create 400 "1x400g" 200 "2x200g" 100 [expr {$ARCHGRP_ARR(ETH_PORT_CHAN,0) == 2 ? "2x100g" : "4x100g"}] 50 "8x50g" 40 "2x40g" 25 "8x25g" 10 "8x10g"]
set FTILE_ETH_IP_NAME "ftile_eth_[dict get $ETH_CONF $ARCHGRP_ARR(ETH_PORT_SPEED,0)]"

set ETH_MR_CONF [dict create 100 "1x100g" 25 "1x25g_1x10g"]
set FTILE_MR_ETH_IP_NAME ""
if {$ARCHGRP_ARR(EHIP_PORT_TYPE,0) == 1} {
    set FTILE_MR_ETH_IP_NAME "ftile_multirate_eth_[dict get $ETH_MR_CONF $ARCHGRP_ARR(ETH_PORT_SPEED,0)]"
}

# see '$ARCHGRP_ARR(CORE_BASE)/src/ip/common.tcl' for more information regarding the fields
#                         script_path     script_name        ip_comp_name       type  modify
lappend IP_COMPONENTS [list  "clk"     "ftile_pll"         "ftile_pll"            0      1]
lappend IP_COMPONENTS [list  "clk"     "iopll"             "iopll_ip"             0      1]
lappend IP_COMPONENTS [list  "mem"     "ddr4_calibration"  "emif_agi027_cal"      0      1]
lappend IP_COMPONENTS [list  "mem"     "ddr4_calibration"  "sodimm_cal"           1      1]
lappend IP_COMPONENTS [list  "mem"     "onboard_ddr4"      "OnBoard_DDR4"         0      1]
lappend IP_COMPONENTS [list  "mem"     "onboard_ddr4"      "sodimm"               1      1]
lappend IP_COMPONENTS [list  "misc"    "mailbox_client"    "mailbox_client_ip"    0      0]
lappend IP_COMPONENTS [list  "misc"    "reset_release"     "reset_release_ip"     0      0]
lappend IP_COMPONENTS [list  "pcie"    "rtile_pcie"        $RTILE_PCIE_IP_NAME    0      1]

if {$ARCHGRP_ARR(VIRTUAL_DEBUG_ENABLE)} {
    lappend IP_COMPONENTS [list "misc"  "jtag_op"          "jtag_op_ip"           0      0]
}

if {$ARCHGRP_ARR(NET_MOD_ARCH) eq "F_TILE"} {
    if {$ARCHGRP_ARR(EHIP_PORT_TYPE,0) == 1} {
        lappend IP_COMPONENTS [list "eth"  "ftile_mr_eth"  $FTILE_MR_ETH_IP_NAME  0      1]
        lappend IP_COMPONENTS [list "eth"  "dr_ctrl"       "dr_ctrl"              0      1]
    } else {
        lappend IP_COMPONENTS [list "eth"  "ftile_eth"     $FTILE_ETH_IP_NAME     0      1]
    }
}

lappend MOD {*}[get_ip_mod_files $IP_COMPONENTS [array get ARCHGRP_ARR]]

# Top-level
lappend MOD "$OFM_PATH/comp/ctrls/flash/flashctrl.vhd"
lappend MOD "$ENTITY_BASE/fpga.vhd"
