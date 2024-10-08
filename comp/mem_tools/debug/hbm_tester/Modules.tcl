# Modules.tcl: Components include script
# Copyright (C) 2024 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE                    "$OFM_PATH/comp/base/pkg"
set BIN2HOT_BASE                "$OFM_PATH/comp/base/logic/bin2hot"
set LFSR_SIMPLE_RANDOM_GEN_BASE "$OFM_PATH/comp/base/logic/lfsr_simple_random_gen"
set PIPE_BASE                   "$OFM_PATH/comp/base/misc/pipe"
set MI32_ASYNC_HANDSHAKE_BASE   "$OFM_PATH/comp/mi_tools/async"

lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

lappend COMPONENTS [list "BIN2HOT"                $BIN2HOT_BASE                "FULL" ]
lappend COMPONENTS [list "LFSR_SIMPLE_RANDOM_GEN" $LFSR_SIMPLE_RANDOM_GEN_BASE "FULL" ]
lappend COMPONENTS [list "PIPE"                   $PIPE_BASE                   "FULL" ]
lappend COMPONENTS [list "MI32_ASYNC_HANDSHAKE"   $MI32_ASYNC_HANDSHAKE_BASE   "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/comp/hbm_tester_gen.vhd"
lappend MOD "$ENTITY_BASE/comp/hbm_tester_mon.vhd"
lappend MOD "$ENTITY_BASE/comp/hbm_tester_port.vhd"
lappend MOD "$ENTITY_BASE/comp/hbm_tester_adc.vhd"
lappend MOD "$ENTITY_BASE/hbm_tester.vhd"
lappend MOD "$ENTITY_BASE/DevTree.tcl"
