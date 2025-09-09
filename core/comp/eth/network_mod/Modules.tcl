# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# convert input list to an array
array set ARCHGRP_ARR $ARCHGRP
set NET_MOD_ARCH $ARCHGRP_ARR(NET_MOD_ARCH)

# Paths to components
set ASYNC_RESET_BASE          "$OFM_PATH/comp/base/async/reset"
set ASYNC_OPENLOOP_BASE       "$OFM_PATH/comp/base/async/open_loop"
set MI_SPLITTER_BASE          "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set NETWORK_MOD_COMP_BASE     "$ENTITY_BASE/comp"
set NETWORK_MOD_CORE_BASE     "$NETWORK_MOD_COMP_BASE/network_mod_core"
set NETWORK_MOD_LOG_BASE      "$NETWORK_MOD_COMP_BASE/network_mod_logic"
set I2C_BASE                  "$OFM_PATH/comp/ctrls/i2c_hw"
set ASFIFOX_BASE              "$OFM_PATH/comp/base/fifo/asfifox"
set TSU_ASYNC_BASE            "$OFM_PATH/comp/tsu/tsu_async"
set NM_LOGIC_ARCHGRP          "NO_CRC"

# Set path to external network module in your application (app_conf.tcl) compatible with ndk-fpga
# set NET_MOD_EXT_BASE "<path_to_custom_net_mod>"
# The target directory should contain at least Modules.tcl that will collect other neccessary parts of network_module

# Example:
# set NET_MOD_EXT_BASE "$OFM_PATH/../comp/eth/network_mod/"
#
# ndk-app-example/
# ├── comp/
# │    ├── eth/
# │         ├── netowork_mod/
# │              ├── network_mod.vhd
# │              ├── Modules.tcl
# │              ├── DevTree.tcl
# ├── ndk-fpga/
# ...

if {[info exists ARCHGRP_ARR(NET_MOD_EXT_BASE)]} {
    set EXTERNAL_BASE   "$ARCHGRP_ARR(NET_MOD_EXT_BASE)"
} elseif {$NET_MOD_ARCH == "EXTERNAL"} {
    error "ERROR: Missing external path. Set NET_MOD_EXT_BASE variable in app_conf.tcl located in application build directory"
}

# uncomment only for local synthesis
# options: F_TILE, E_TILE, CMAC
# set ARCHGRP  "F_TILE"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/eth_hdr_pack.vhd"

lappend MOD "$ENTITY_BASE/network_mod_ent.vhd"

if {$NET_MOD_ARCH == "EMPTY"} {
    lappend MOD "$ENTITY_BASE/network_mod_empty.vhd"
} elseif {$NET_MOD_ARCH == "EXTERNAL"} {
    lappend COMPONENTS [list "NETWORK_MOD"          $EXTERNAL_BASE         "FULL"           ]
} else {
    if { $NET_MOD_ARCH == "10G4" || $NET_MOD_ARCH == "25G4" || $NET_MOD_ARCH == "40GE"} {
        set NM_LOGIC_ARCHGRP "FULL"
    }
    lappend COMPONENTS [list "ASYNC_OPENLOOP"       $ASYNC_OPENLOOP_BASE   "FULL"           ]
    lappend COMPONENTS [list "ASYNC_RESET"          $ASYNC_RESET_BASE      "FULL"           ]
    lappend COMPONENTS [list "MI_SPLITTER_PLUS_GEN" $MI_SPLITTER_BASE      "FULL"           ]
    lappend COMPONENTS [list "NETWORK_MOD_CORE"     $NETWORK_MOD_CORE_BASE $NET_MOD_ARCH    ]
    lappend COMPONENTS [list "NETWORK_MOD_LOGIC"    $NETWORK_MOD_LOG_BASE  $NM_LOGIC_ARCHGRP]
    lappend COMPONENTS [list "I2C_CTRL"             $I2C_BASE              "FULL"           ]
    lappend COMPONENTS [list "ASFIFOX"              $ASFIFOX_BASE          "FULL"           ]
    lappend COMPONENTS [list "TSU_ASYNC"            $TSU_ASYNC_BASE        "FULL"           ]

    # Source files for implemented component
    lappend MOD "$ENTITY_BASE/qsfp_ctrl.vhd"
    lappend MOD "$ENTITY_BASE/network_mod.vhd"
    lappend MOD "$ENTITY_BASE/DevTree.tcl"
}
