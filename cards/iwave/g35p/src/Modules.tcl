# Modules.tcl: script to compile iWave G35P
# Copyright (C) 2024 DynaNIC Semiconductors, Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# converting input list to associative array
array set ARCHGRP_ARR $ARCHGRP

# Paths
set FPGA_COMMON_BASE "$ARCHGRP_ARR(CORE_BASE)/top"

# Components
lappend COMPONENTS [list "FPGA_COMMON"  $FPGA_COMMON_BASE   $ARCHGRP]

# IP components
source $ARCHGRP_ARR(IP_TEMPLATE_ROOT)/common.tcl

set ARCHGRP_ARR(IP_MODIFY_BASE)   $ENTITY_BASE/ip
set ARCHGRP_ARR(USE_IP_SUBDIRS)   true

lappend IP_COMPONENTS [list "eth"    "cmac_eth_1x100g"    "cmac_eth_1x100g"      0  1]
lappend IP_COMPONENTS [list "pcie"   "pcie4_uscale_plus"  "pcie4_uscale_plus"    0  1]

lappend MOD {*}[get_ip_mod_files $IP_COMPONENTS [array get ARCHGRP_ARR]]

# Top-level
lappend MOD "$ENTITY_BASE/fpga.vhd"
