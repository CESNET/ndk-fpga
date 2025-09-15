# Modules.tcl: script to compile card
# Copyright (C) 2025 DynaNIC Semiconductors ltd.
# Author(s): Vlastimil Kosar <kosarl@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# converting input list to associative array
array set ARCHGRP_ARR $ARCHGRP

set OFS_BASE       "$OFM_PATH/extra/ip-3rdparty/silicom/n5014/pmci-spi"
set HBM_RESET_BASE "$ENTITY_BASE/comp/hbm"

# converting input list to associative array
array set ARCHGRP_ARR $ARCHGRP
set FPGA_COMMON_BASE "$ARCHGRP_ARR(CORE_BASE)/top"

lappend COMPONENTS [list "FPGA_COMMON"       $FPGA_COMMON_BASE     $ARCHGRP]
lappend COMPONENTS [list "OFS"               $OFS_BASE               "FULL"]
lappend COMPONENTS [list "HBM_RESET"         $HBM_RESET_BASE         "FULL"]

# IP components
set IP_COMMON_TCL $ARCHGRP_ARR(IP_TEMPLATE_ROOT)/common.tcl
source $IP_COMMON_TCL

set ARCHGRP_ARR(IP_COMMON_TCL)    $IP_COMMON_TCL
set ARCHGRP_ARR(IP_TEMPLATE_BASE) $ARCHGRP_ARR(IP_TEMPLATE_ROOT)/intel
set ARCHGRP_ARR(IP_MODIFY_BASE)   $ENTITY_BASE/ip
set ARCHGRP_ARR(IP_DEVICE_FAMILY) "Stratix 10"
set ARCHGRP_ARR(IP_DEVICE)        $ARCHGRP_ARR(FPGA)

# see '$ARCHGRP_ARR(CORE_BASE)/src/ip/common.tcl' for more information regarding the fields
#                         script_path    script_name       ip_comp_name             type  modify

lappend IP_COMPONENTS [list  "clk"    "iopll"             "iopll_ip"                  0      1]
lappend IP_COMPONENTS [list  "misc"   "mailbox_client"    "mailbox_client_ip"         0      0]
lappend IP_COMPONENTS [list  "misc"   "reset_release"     "reset_release_ip"          0      0]
lappend IP_COMPONENTS [list  "mem"    "hbm"               "hbm_top"                   0      1]
lappend IP_COMPONENTS [list  "mem"    "hbm"               "hbm_bottom"                1      1]
lappend IP_COMPONENTS [list  "mem"    "onboard_ddr4_s10"  "emif_ddr4_x64_ecc_bank0"   0      1]
lappend IP_COMPONENTS [list  "mem"    "onboard_ddr4_s10"  "emif_ddr4_x64_ecc_bank1"   1      1]

if {$ARCHGRP_ARR(PCIE_ENDPOINT_MODE) == 0} {
    lappend IP_COMPONENTS [list  "pcie"   "ptile_pcie"        "ptile_pcie_1x16"           0      1]
}

if {$ARCHGRP_ARR(NET_MOD_ARCH) == "E_TILE"} {
    if {$ARCHGRP_ARR(ETH_PORT_SPEED,0) == 100} {
        lappend IP_COMPONENTS [list  "eth"    "etile_eth_s10"     "etile_eth_1x100g"          0      1]
    }
}

lappend MOD {*}[get_ip_mod_files $IP_COMPONENTS [array get ARCHGRP_ARR]]

# Top-level
lappend MOD "$ENTITY_BASE/fpga.vhd"

lappend MOD "$ENTITY_BASE/DevTree.tcl"
