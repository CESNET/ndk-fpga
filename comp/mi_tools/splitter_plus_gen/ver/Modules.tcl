# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SV_MI_BASE   "$OFM_PATH/comp/mi_tools/ver"

set COMPONENTS [list \
      [ list "SV_MI"   $SV_MI_BASE  "UNIFIED"]   \
]

set MOD "$MOD $ENTITY_BASE/mi_splitter_plus_gen_wrapper.vhd"

set MOD "$MOD $ENTITY_BASE/tbench/scoreboard.sv"
set MOD "$MOD $ENTITY_BASE/tbench/sequence.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
