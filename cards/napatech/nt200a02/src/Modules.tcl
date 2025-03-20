# Modules.tcl: script to compile card
# Copyright (C) 2025 DynaNIC Semiconductors s.r.o.
# Author(s): Jan Privara <privara@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# converting input list to associative array
array set ARCHGRP_ARR $ARCHGRP

# Paths
set FPGA_COMMON_BASE         "$ARCHGRP_ARR(CORE_BASE)/top"
set BOOT_CTRL_BASE           "$OFM_PATH/core/comp/misc/boot_ctrl"
set AXI_QSPI_FLASH_CTRL_BASE "$ENTITY_BASE/comp/axi_quad_flash_controller"

# Components
lappend COMPONENTS [list "FPGA_COMMON"         $FPGA_COMMON_BASE         $ARCHGRP]
lappend COMPONENTS [list "BOOT_CTRL"           $BOOT_CTRL_BASE           "FULL"  ]
lappend COMPONENTS [list "AXI_QSPI_FLASH_CTRL" $AXI_QSPI_FLASH_CTRL_BASE "FULL"  ]

# IP components
source $ARCHGRP_ARR(IP_TEMPLATE_ROOT)/common.tcl

set ARCHGRP_ARR(IP_MODIFY_BASE)   $ENTITY_BASE/ip
set ARCHGRP_ARR(USE_IP_SUBDIRS)   true

lappend IP_COMPONENTS [list "mem"    "axi_quad_spi_0"     "axi_quad_spi_0"       0  1]
lappend IP_COMPONENTS [list "eth"    "cmac_eth_1x100g"    "cmac_eth_1x100g"      0  1]
lappend IP_COMPONENTS [list "pcie"   "pcie4_uscale_plus"  "pcie4_uscale_plus"    0  1]

lappend MOD {*}[get_ip_mod_files $IP_COMPONENTS [array get ARCHGRP_ARR]]

# Top-level
lappend MOD "$ENTITY_BASE/fpga.vhd"
