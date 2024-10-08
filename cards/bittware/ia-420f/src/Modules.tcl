# Modules.tcl: script to compile IA-420F card
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz.cz>
#            Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set IOEXP_BASE "$OFM_PATH/comp/ctrls/i2c_io_exp"
set ASYNC_BASE "$OFM_PATH/comp/base/async"

# converting input list to associative array
array set ARCHGRP_ARR $ARCHGRP

lappend COMPONENTS [list "FPGA_COMMON"       $ARCHGRP_ARR(CORE_BASE) $ARCHGRP]
lappend COMPONENTS [list "I2C IO EXPANDER"   $IOEXP_BASE               "FULL"]
lappend COMPONENTS [list "OPEN_LOOP"         $ASYNC_BASE/open_loop     "FULL"]
lappend COMPONENTS [list "RESET"             $ASYNC_BASE/reset         "FULL"]

# IP components
source $ARCHGRP_ARR(CORE_BASE)/src/ip/common.tcl

set ARCHGRP_ARR(IP_TEMPLATE_BASE) $ARCHGRP_ARR(CORE_BASE)/src/ip/intel
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
lappend IP_COMPONENTS [list  "mem"    "ddr4_calibration" "ddr4_calibration"   0      0]
lappend IP_COMPONENTS [list  "mem"    "onboard_ddr4"     "onboard_ddr4_0"     0      1]
lappend IP_COMPONENTS [list  "mem"    "onboard_ddr4"     "onboard_ddr4_1"     1      1]
lappend IP_COMPONENTS [list  "misc"   "mailbox_client"   "mailbox_client_ip"  0      0]
lappend IP_COMPONENTS [list  "misc"   "reset_release"    "reset_release_ip"   0      0]
lappend IP_COMPONENTS [list  "pcie"   "ptile_pcie"       $PTILE_PCIE_IP_NAME  0      1]

if {$ARCHGRP_ARR(VIRTUAL_DEBUG_ENABLE)} {
    lappend IP_COMPONENTS [list "misc"  "jtag_op"        "jtag_op_ip"         0      0]
}

if {$ARCHGRP_ARR(NET_MOD_ARCH) eq "E_TILE"} {
    lappend IP_COMPONENTS [list "eth"   "etile_eth"      $ETILE_ETH_IP_NAME   0      1]
}

lappend MOD {*}[get_ip_mod_files $IP_COMPONENTS [array get ARCHGRP_ARR]]

# Top-level
lappend MOD "$ENTITY_BASE/fpga.vhd"
