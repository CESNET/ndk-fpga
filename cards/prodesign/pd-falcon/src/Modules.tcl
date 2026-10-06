# Modules.tcl: script to compile PD-FALCON card
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Denis Kurka <xkurka05@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# converting input list to associative array
array set ARCHGRP_ARR $ARCHGRP

# Paths
set FPGA_COMMON_BASE "$ARCHGRP_ARR(CORE_BASE)/top"

lappend COMPONENTS [list "FPGA_COMMON" $FPGA_COMMON_BASE $ARCHGRP]

# IP sources
lappend MOD "$ENTITY_BASE/ip/iopll_ip.ip"
lappend MOD "$ENTITY_BASE/ip/reset_release_ip.ip"
lappend MOD "$ENTITY_BASE/ip/etile_eth_1x100g.ip"
lappend MOD "$ENTITY_BASE/ip/mailbox_client_ip.ip"

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
lappend IP_COMPONENTS [list  "pcie"   "htile_pcie"        "htile_pcie_1x16"           0      1]

lappend MOD {*}[get_ip_mod_files $IP_COMPONENTS [array get ARCHGRP_ARR]]

# Top-level
lappend MOD "$ENTITY_BASE/fpga.vhd"
