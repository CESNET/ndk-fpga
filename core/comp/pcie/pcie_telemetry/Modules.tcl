# Modules.tcl: script to compile single module
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Component paths
set ASFIFOX_BASE        "$OFM_PATH/comp/base/fifo/asfifox"
set OPEN_LOOP_BASE      "$OFM_PATH/comp/base/async/open_loop"
set ASYNC_RESET_BASE    "$OFM_PATH/comp/base/async/reset"
set BUS_HANDSHAKE_BASE  "$OFM_PATH/comp/base/async/bus_handshake"
set DP_BRAM_BASE        "$OFM_PATH/comp/base/mem/dp_bram"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "ASFIFOX"              $ASFIFOX_BASE       "FULL" ]
lappend COMPONENTS [ list "ASYNC_OPEN_LOOP"      $OPEN_LOOP_BASE     "FULL" ]
lappend COMPONENTS [ list "ASYNC_RESET"          $ASYNC_RESET_BASE   "FULL" ]
lappend COMPONENTS [ list "ASYNC_BUS_HANDSHAKE"  $BUS_HANDSHAKE_BASE "FULL" ]
lappend COMPONENTS [ list "DP_BRAM_BEHAV"        $DP_BRAM_BASE       "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/comp/pcie_telemetry_probe.vhd"
lappend MOD "$ENTITY_BASE/comp/pcie_telemetry_acc.vhd"
lappend MOD "$ENTITY_BASE/pcie_telemetry_mi.vhd"
lappend MOD "$ENTITY_BASE/DevTree.tcl"
