# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set ASYNC_RESET_BASE          "$OFM_PATH/comp/base/async/reset"
set ASYNC_OPENLOOP_BASE       "$OFM_PATH/comp/base/async/open_loop"
set MI_SPLITTER_BASE          "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set NETWORK_MOD_COMP_BASE     "$ENTITY_BASE/comp"
set NETWORK_MOD_CORE_BASE     "$NETWORK_MOD_COMP_BASE/network_mod_core"
set NETWORK_MOD_LOG_BASE      "$NETWORK_MOD_COMP_BASE/network_mod_logic"
set I2C_BASE                  "$OFM_PATH/comp/ctrls/i2c_hw"
set ASFIFOX_BASE              "$OFM_PATH/comp/base/fifo/asfifox"

# uncomment only for local synthesis
# options: F_TILE, E_TILE, CMAC
# set ARCHGRP  "F_TILE"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/eth_hdr_pack.vhd"

lappend MOD "$ENTITY_BASE/network_mod_ent.vhd"

if {$ARCHGRP == "EMPTY"} {
    lappend MOD "$ENTITY_BASE/network_mod_empty.vhd"
} else {
    lappend COMPONENTS [list "ASYNC_OPENLOOP"       $ASYNC_OPENLOOP_BASE   "FULL"  ]
    lappend COMPONENTS [list "ASYNC_RESET"          $ASYNC_RESET_BASE      "FULL"  ]
    lappend COMPONENTS [list "MI_SPLITTER_PLUS_GEN" $MI_SPLITTER_BASE      "FULL"  ]
    lappend COMPONENTS [list "NETWORK_MOD_CORE"     $NETWORK_MOD_CORE_BASE $ARCHGRP]
    lappend COMPONENTS [list "NETWORK_MOD_LOGIC"    $NETWORK_MOD_LOG_BASE  "FULL"  ]
    lappend COMPONENTS [list "I2C_CTRL"             $I2C_BASE              "FULL"  ]
    lappend COMPONENTS [list "ASFIFOX"              $ASFIFOX_BASE          "FULL"  ]

    # Source files for implemented component
    lappend MOD "$ENTITY_BASE/qsfp_ctrl.vhd"
    lappend MOD "$ENTITY_BASE/network_mod.vhd"
    lappend MOD "$ENTITY_BASE/DevTree.tcl"
}
