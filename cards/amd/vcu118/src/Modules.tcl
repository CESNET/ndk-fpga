# Modules.tcl: script to compile card
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Vladislav Valek <xvalek14@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# converting input list to associative array
array set ARCHGRP_ARR $ARCHGRP

# Components
lappend COMPONENTS [list "FPGA_COMMON"      $ARCHGRP_ARR(CORE_BASE)  $ARCHGRP]

# IP sources
if {$ARCHGRP_ARR(PCIE_ENDPOINT_MODE) == 2} {
    lappend MOD "$ENTITY_BASE/ip/pcie4_uscale_plus/x8_low_latency/pcie4_uscale_plus.xci"
} else {
    lappend MOD "$ENTITY_BASE/ip/pcie4_uscale_plus/x16/pcie4_uscale_plus.xci"
}

if {$ARCHGRP_ARR(VIRTUAL_DEBUG_ENABLE)} {
    lappend MOD "$ENTITY_BASE/ip/xvc_vsec/xvc_vsec.xci"
}

if {$ARCHGRP_ARR(NET_MOD_ARCH) != "EMPTY"} {
    lappend MOD "$ENTITY_BASE/ip/cmac_eth_1x100g/cmac_eth_1x100g.xci"
}

# lappend MOD "$ENTITY_BASE/ip/ddr4_axi/ddr4_axi.xci"

# Top-level
lappend MOD "$ENTITY_BASE/fpga.vhd"
