# Modules.tcl: script to compile DK-DEV-1SDX-P card
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# converting input list to associative array
array set ARCHGRP_ARR $ARCHGRP

set COMPONENTS [list [list "FPGA_COMMON" $ARCHGRP_ARR(CORE_BASE) $ARCHGRP]]

# IP sources
set MOD "$MOD $ENTITY_BASE/ip/iopll_ip.ip"
set MOD "$MOD $ENTITY_BASE/ip/reset_release_ip.ip"
set MOD "$MOD $ENTITY_BASE/ip/ptile_pcie_2x8.ip"
set MOD "$MOD $ENTITY_BASE/ip/ptile_pcie_1x16.ip"
set MOD "$MOD $ENTITY_BASE/ip/etile_eth_4x10g.ip"
set MOD "$MOD $ENTITY_BASE/ip/etile_eth_4x25g.ip"
set MOD "$MOD $ENTITY_BASE/ip/etile_eth_1x100g.ip"
set MOD "$MOD $ENTITY_BASE/ip/emif_s10dx.ip"
set MOD "$MOD $ENTITY_BASE/ip/mailbox_client_ip.ip"

# Top-level
set MOD "$MOD $ENTITY_BASE/fpga.vhd"
