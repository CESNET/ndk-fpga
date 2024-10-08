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
lappend MOD "$ENTITY_BASE/ip/htile_pcie_1x16.ip"
lappend MOD "$ENTITY_BASE/ip/mailbox_client_ip.ip"

# Top-level
lappend MOD "$ENTITY_BASE/fpga.vhd"
