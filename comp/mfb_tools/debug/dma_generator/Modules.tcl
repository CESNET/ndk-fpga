# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set MFB_GENERATOR_MI32_BASE   "$OFM_PATH/comp/mfb_tools/debug/generator"
set MI32_ASYNC_HANDSHAKE_BASE "$OFM_PATH/comp/mi_tools/async"
set MI32_PIPE_BASE            "$OFM_PATH/comp/mi_tools/pipe"

set COMPONENTS [list \
    [ list "MFB_GENERATOR_MI32"   $MFB_GENERATOR_MI32_BASE   "FULL" ] \
    [ list "MI32_ASYNC_HANDSHAKE" $MI32_ASYNC_HANDSHAKE_BASE "FULL" ] \
    [ list "MI32_PIPE"            $MI32_PIPE_BASE            "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/dma_mfb_generator.vhd"
