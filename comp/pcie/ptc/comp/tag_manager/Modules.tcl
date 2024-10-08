# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

# SPDX-License-Identifier: BSD-3-Clause
# Set paths

set GEN_ENC_BASE       "$OFM_PATH/comp/base/logic/enc"
set GEN_NOR_BASE       "$OFM_PATH/comp/base/logic/gen_nor"
set FIFOXM_BASE        "$OFM_PATH/comp/base/fifo/fifox_multi"
set TREE_ADDER_BASE    "$OFM_PATH/comp/base/logic/pipe_tree_adder"
set N_LOOP_OP_BASE     "$OFM_PATH/comp/base/logic/n_loop_op"
set SHAKEDOWN_BASE     "$OFM_PATH/comp/mvb_tools/flow/merge_n_to_m"

# Packages
set PKG_BASE "$OFM_PATH/comp/base/pkg"
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/dma_bus_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/ver/vhdl_ver_tools/basics/basics_test_pkg.vhd"

# list of sub-components
set COMPONENTS [list \
    [ list "GEN_ENC"         $GEN_ENC_BASE    "FULL" ] \
    [ list "GEN_NOR"         $GEN_NOR_BASE    "FULL" ] \
    [ list "FIFOX_MULTI"     $FIFOXM_BASE     "FULL" ] \
    [ list "PIPE_TREE_ADDER" $TREE_ADDER_BASE "FULL" ] \
    [ list "N_LOOP_OP"       $N_LOOP_OP_BASE  "FULL" ] \
    [ list "SHAKEDOWN"       $SHAKEDOWN_BASE  "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/ptc_tag_manager.vhd"
