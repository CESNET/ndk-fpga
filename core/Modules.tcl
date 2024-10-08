# Modules.tcl: script to compile single module
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#           Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: For more information, visit the Parametrization section of the NDK-CORE documentation.

# convert input list to an array
array set ARCHGRP_ARR $ARCHGRP

# Paths to components
set ASYNC_RESET_BASE     "$OFM_PATH/comp/base/async/reset"
set ASYNC_OPEN_LOOP_BASE "$OFM_PATH/comp/base/async/open_loop"
set TSU_BASE             "$OFM_PATH/comp/tsu/tsu_gen"
set PCIE_BASE            "$ENTITY_BASE/src/comp/pcie"
set DMA_BASE             "$ENTITY_BASE/src/comp/dma"
set NETWORK_MOD_BASE     "$ENTITY_BASE/src/comp/network_mod"
set CLOCK_GEN_BASE       "$ENTITY_BASE/src/comp/clk_gen"
set SDM_CTRL_BASE        "$ENTITY_BASE/src/comp/sdm_ctrl"
set MI_SPLITTER_BASE     "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set RESET_TREE_GEN_BASE  "$OFM_PATH/comp/base/misc/reset_tree_gen"
set MI_TEST_SPACE_BASE   "$OFM_PATH/comp/mi_tools/test_space"
set DMA_GENERATOR_BASE   "$OFM_PATH/comp/mfb_tools/debug/dma_generator"
set HWID_BASE            "$OFM_PATH/comp/base/misc/hwid"
set ETH_LED_CTRL_BASE    "$OFM_PATH/comp/nic/eth_leds/led_ctrl_top"
set JTAG_OP_CTRL_BASE    "$ENTITY_BASE/src/comp/jtag_op_ctrl"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/dma_bus_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/eth_hdr_pack.vhd"
lappend PACKAGES "$ENTITY_BASE/config/core_const.vhd"
lappend PACKAGES "$ENTITY_BASE/src/mi_addr_space_pkg.vhd"

if { $ARCHGRP_ARR(APPLICATION_CORE_ENTITY_ONLY) } {
  lappend MOD "$ENTITY_BASE/src/application_ent.vhd"
} else {

  set DMA_ARCH "EMPTY"

  if { $ARCHGRP_ARR(DMA_TYPE) == 3 } {
      set DMA_ARCH "MEDUSA"
  } elseif {$ARCHGRP_ARR(DMA_TYPE) == 4} {
      set DMA_ARCH "CALYPTE"
  }

  set JTAG_OP_ARCH "EMPTY"

  if { $ARCHGRP_ARR(VIRTUAL_DEBUG_ENABLE) eq true } {
    set JTAG_OP_ARCH $ARCHGRP_ARR(CLOCK_GEN_ARCH)
  }

  lappend COMPONENTS [list "CLOCK_GEN"       $CLOCK_GEN_BASE       $ARCHGRP_ARR(CLOCK_GEN_ARCH) ]
  lappend COMPONENTS [list "SDM_CTRL"        $SDM_CTRL_BASE        $ARCHGRP_ARR(SDM_SYSMON_ARCH)]
  lappend COMPONENTS [list "ASYNC_RESET"     $ASYNC_RESET_BASE     "FULL"                       ]
  lappend COMPONENTS [list "ASYNC_OPEN_LOOP" $ASYNC_OPEN_LOOP_BASE "FULL"                       ]
  lappend COMPONENTS [list "TSU"             $TSU_BASE             "FULL"                       ]
  lappend COMPONENTS [list "HWID"            $HWID_BASE            $ARCHGRP_ARR(CLOCK_GEN_ARCH) ]
  lappend COMPONENTS [list "RESET_TREE_GEN"  $RESET_TREE_GEN_BASE  "FULL"                       ]
  lappend COMPONENTS [list "PCIE"            $PCIE_BASE            $ARCHGRP_ARR(PCIE_MOD_ARCH)  ]
  lappend COMPONENTS [list "MI_SPLITTER"     $MI_SPLITTER_BASE     "FULL"                       ]
  lappend COMPONENTS [list "MI_TEST_SPACE"   $MI_TEST_SPACE_BASE   "FULL"                       ]
  lappend COMPONENTS [list "NETWORK_MOD"     $NETWORK_MOD_BASE     $ARCHGRP_ARR(NET_MOD_ARCH)   ]
  lappend COMPONENTS [list "ETH_LED_CTRL"    $ETH_LED_CTRL_BASE    "FULL"                       ]
  lappend COMPONENTS [list "DMA"             $DMA_BASE             $DMA_ARCH                    ]
  lappend COMPONENTS [list "DMA_GENERATOR"   $DMA_GENERATOR_BASE   "FULL"                       ]
  lappend COMPONENTS [list "JTAG_OP_CTRL"    $JTAG_OP_CTRL_BASE    $JTAG_OP_ARCH                ]

  lappend MOD "$ENTITY_BASE/src/application_ent.vhd"
  lappend MOD "$ENTITY_BASE/src/fpga_common.vhd"
  lappend MOD "$ENTITY_BASE/src/DevTree.tcl"
}
