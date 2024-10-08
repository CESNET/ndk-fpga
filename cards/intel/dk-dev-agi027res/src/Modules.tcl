# Modules.tcl: script to compile DK-DEV-AGI027RES card
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# converting input list to associative array
array set ARCHGRP_ARR $ARCHGRP

# Paths to components
set ASYNC_OPEN_LOOP_BASE    "$OFM_PATH/comp/base/async/open_loop"
set EMIF_REFRESH_BASE       "$OFM_PATH/comp/debug/mem_tester/emif_refresh"

set COMPONENTS [concat $COMPONENTS [list \
    [list "FPGA_COMMON"     $ARCHGRP_ARR(CORE_BASE) $ARCHGRP] \
    [list "ASYNC_OPEN_LOOP" $ASYNC_OPEN_LOOP_BASE   "FULL"  ] \
    [list "EMIF_REFRESH"    $EMIF_REFRESH_BASE      "FULL"  ] \
]]

# IP sources
set MOD "$MOD $ENTITY_BASE/ip/iopll_ip.ip"
set MOD "$MOD $ENTITY_BASE/ip/reset_release_ip.ip"
set MOD "$MOD $ENTITY_BASE/ip/rtile_pcie_2x8.ip"
set MOD "$MOD $ENTITY_BASE/ip/rtile_pcie_1x16.ip"
set MOD "$MOD $ENTITY_BASE/ip/emif_agi027.ip"
set MOD "$MOD $ENTITY_BASE/ip/emif_agi027_cal.ip"
set MOD "$MOD $ENTITY_BASE/ip/mailbox_client_ip.ip"
set MOD "$MOD $ENTITY_BASE/ip/ftile_pll.ip"

if {$ARCHGRP_ARR(NET_MOD_ARCH) == "F_TILE"} {
    if {$ARCHGRP_ARR(ETH_PORT_SPEED,0) == 400} {
        set MOD "$MOD $ENTITY_BASE/ip/ftile_eth_1x400g.ip"
    }
    if {$ARCHGRP_ARR(ETH_PORT_SPEED,0) == 200} {
        set MOD "$MOD $ENTITY_BASE/ip/ftile_eth_2x200g.ip"
    }
    if {$ARCHGRP_ARR(ETH_PORT_SPEED,0) == 100} {
        set MOD "$MOD $ENTITY_BASE/ip/ftile_eth_4x100g.ip"
    }
    if {$ARCHGRP_ARR(ETH_PORT_SPEED,0) == 50} {
        set MOD "$MOD $ENTITY_BASE/ip/ftile_eth_8x50g.ip"
    }
    if {$ARCHGRP_ARR(ETH_PORT_SPEED,0) == 40} {
        set MOD "$MOD $ENTITY_BASE/ip/ftile_eth_2x40g.ip"
    }
    if {$ARCHGRP_ARR(ETH_PORT_SPEED,0) == 25} {
        set MOD "$MOD $ENTITY_BASE/ip/ftile_eth_8x25g.ip"
    }
    if {$ARCHGRP_ARR(ETH_PORT_SPEED,0) == 10} {
        set MOD "$MOD $ENTITY_BASE/ip/ftile_eth_8x10g.ip"
    }
}

# Top-level
set MOD "$MOD $ENTITY_BASE/fpga.vhd"
