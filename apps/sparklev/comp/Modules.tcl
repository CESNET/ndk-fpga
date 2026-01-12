# Modules.tcl: script to compile single module
# Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

# converting input list to associative array (uncomment when needed)
array set ARCHGRP_ARR $ARCHGRP

# Component paths
set ASYNC_RESET_BASE         "$OFM_PATH/comp/base/async/reset"
set RESET_TREE_GEN_BASE      "$OFM_PATH/comp/base/misc/reset_tree_gen"
set PCIE_BASE                "$ARCHGRP_ARR(CORE_BASE)/comp/pcie/pcie_mod"
set ASYNC_OPEN_LOOP_BASE     "$OFM_PATH/comp/base/async/open_loop"
set ASYNC_OPEN_LOOP_SMD_BASE "$OFM_PATH/comp/base/async/open_loop_smd"
set MI_SPLITTER_BASE         "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set MI_TEST_SPACE_BASE       "$OFM_PATH/comp/mi_tools/test_space"
set SDM_CTRL_BASE            "$ARCHGRP_ARR(CORE_BASE)/comp/misc/sdm_ctrl"
set HWID_BASE                "$OFM_PATH/comp/base/misc/hwid"
set DMA_BASE                 "$ENTITY_BASE/comp/dma"
set BOOT_CTRL_BASE           "$OFM_PATH/core/comp/misc/boot_ctrl"
set AXI_QSPI_FLASH_CTRL_BASE "$OFM_PATH/cards/silicom/fb2cghh/src/comp/axi_quad_flash_controller"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$ARCHGRP_ARR(CORE_BASE)/config/core_const.vhd"
lappend PACKAGES "$ENTITY_BASE/mi_addr_space_pkg.vhd"

# Components
lappend COMPONENTS [list "ASYNC_RESET"          $ASYNC_RESET_BASE           "FULL"                       ]
lappend COMPONENTS [list "RESET_TREE_GEN"       $RESET_TREE_GEN_BASE        "FULL"                       ]
lappend COMPONENTS [list "PCIE"                 $PCIE_BASE                  $ARCHGRP_ARR(PCIE_MOD_ARCH)  ]
lappend COMPONENTS [list "ASYNC_OPEN_LOOP"      $ASYNC_OPEN_LOOP_BASE       "FULL"                       ]
lappend COMPONENTS [list "ASYNC_OPEN_LOOP_SMD"  $ASYNC_OPEN_LOOP_SMD_BASE   "FULL"                       ]
lappend COMPONENTS [list "MI_SPLITTER_PLUS_GEN" $MI_SPLITTER_BASE           "FULL"                       ]
lappend COMPONENTS [list "MI_TEST_SPACE"        $MI_TEST_SPACE_BASE         "FULL"                       ]
lappend COMPONENTS [list "SDM_CTRL"             $SDM_CTRL_BASE              $ARCHGRP_ARR(SDM_SYSMON_ARCH)]
lappend COMPONENTS [list "HWID"                 $HWID_BASE                  $ARCHGRP_ARR(CLOCK_GEN_ARCH) ]
lappend COMPONENTS [list "DMA"                  $DMA_BASE                   "FULL"                       ]
lappend COMPONENTS [list "BOOT_CTRL"            $BOOT_CTRL_BASE             "FULL"                       ]
lappend COMPONENTS [list "AXI_QSPI_FLASH_CTRL"  $AXI_QSPI_FLASH_CTRL_BASE   "FULL"                       ]

lappend IP_COMPONENTS [list "pcie" "pcie4_uscale_plus" "pcie4_uscale_plus" 0 1]
if {$ARCHGRP_ARR(PCIE_ENDPOINTS) == 2 && $ARCHGRP_ARR(PCIE_ENDPOINT_MODE) == 1} {
    lappend IP_COMPONENTS [list "pcie" "pcie4_uscale_plus" "pcie4_uscale_plus_1" 0 1]
}
lappend IP_COMPONENTS [list "mem" "hbm_ip" "hbm_ip" 0 1]
lappend IP_COMPONENTS [list "mem"  "axi_quad_spi"    "axi_quad_spi_0"    0 1]

lappend MOD {*}[get_ip_mod_files $IP_COMPONENTS [array get ARCHGRP_ARR]]

lappend MOD "$ENTITY_BASE/user_core.vhd"
lappend MOD "$ENTITY_BASE/core_logic.vhd"
lappend MOD "$ARCHGRP_ARR(CORE_BASE)/top/DevTree.tcl"
lappend MOD "$ENTITY_BASE/DevTree.tcl"
