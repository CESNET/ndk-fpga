# Modules.tcl: script to compile card
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): David Beneš <xbenes52@vutbr.cz>
#            Vladislav Valek <xvalek14@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# converting input list to associative array
array set ARCHGRP_ARR $ARCHGRP

# Paths
set LED_SERIAL_CTRL_BASE            "$ENTITY_BASE/comp/led_ctrl"
set BMC_BASE                        "$ENTITY_BASE/comp/bmc_driver"
set AXI_QUAD_FLASH_CONTROLLER_BASE  "$ENTITY_BASE/comp/axi_quad_flash_controller"
set BOOT_CTRL_BASE                  "$OFM_PATH/../core/intel/src/comp/boot_ctrl"
set AXI2AVMM_BRIDGE_BASE            "$OFM_PATH/comp/mem_tools/convertors/axi2avmm_ddr_bridge"  

# Components
lappend COMPONENTS [list "FPGA_COMMON"                  $ARCHGRP_ARR(CORE_BASE)          $ARCHGRP]
lappend COMPONENTS [list "LED_SERIAL_CTRL"              $LED_SERIAL_CTRL_BASE            "FULL"  ]
lappend COMPONENTS [list "BMC"                          $BMC_BASE                        "FULL"  ]
lappend COMPONENTS [list "AXI_QUAD_FLASH_CONTROLLER"    $AXI_QUAD_FLASH_CONTROLLER_BASE  "FULL"  ]
lappend COMPONENTS [list "BOOT_CTRL"                    $BOOT_CTRL_BASE                  "FULL"  ]
lappend COMPONENTS [list "AXI2AVMM_BRIDGE"              $AXI2AVMM_BRIDGE_BASE            "FULL"  ]

# IP components
source $ARCHGRP_ARR(CORE_BASE)/src/ip/common.tcl

#set ARCHGRP_ARR(IP_TEMPLATE_BASE) $ARCHGRP_ARR(CORE_BASE)/src/ip/amd
set ARCHGRP_ARR(IP_MODIFY_BASE)   $ENTITY_BASE/ip
set ARCHGRP_ARR(USE_IP_SUBDIRS)   true

# see '$ARCHGRP_ARR(CORE_BASE)/src/ip/common.tcl' for more information regarding the fields
#                         script_path     script_name          ip_comp_name     type  modify
lappend IP_COMPONENTS [list  "mem"    "axi_quad_spi_0"     "axi_quad_spi_0"       0      1]

if {$ARCHGRP_ARR(NET_MOD_ARCH) eq "40GE"} {
    lappend IP_COMPONENTS [list "eth"  "gty_40ge"          "gty_40ge"                     0      1]
} elseif { $ARCHGRP_ARR(NET_MOD_ARCH) eq "25G4" } {
    lappend IP_COMPONENTS [list "eth"  "pcs_pma_4x25g"     "twenty_five_gig_eth_pcspma"   0      1]
} elseif { $ARCHGRP_ARR(NET_MOD_ARCH) eq "10G4" } {
    lappend IP_COMPONENTS [list "eth"  "pcs_pma_4x10g"     "ten_gig_eth_pcspma"           0      1]
} else {
    lappend IP_COMPONENTS [list "eth"  "cmac_eth_1x100g"   "cmac_eth_1x100g"              0      1]
}

if {$ARCHGRP_ARR(MEM_PORTS) > 0} {
    lappend IP_COMPONENTS [list  "mem"    "ddr4_axi"           "ddr4_axi"             0      1]
}

lappend IP_COMPONENTS [list  "pcie"   "pcie4_uscale_plus"  "pcie4_uscale_plus"    0      1]

if {$ARCHGRP_ARR(VIRTUAL_DEBUG_ENABLE)} {
    lappend IP_COMPONENTS [list  "misc"   "xvc_vsec"           "xvc_vsec"             0      1]
}

lappend MOD {*}[get_ip_mod_files $IP_COMPONENTS [array get ARCHGRP_ARR]]

#Simulation
#lappend MOD "$ENTITY_BASE/ip/axi_quad_spi_0/axi_quad_spi_0_sim_netlist.vhdl"

# Top-level
lappend MOD "$ENTITY_BASE/fpga.vhd"
