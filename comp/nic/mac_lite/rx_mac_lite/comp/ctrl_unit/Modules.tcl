# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PKG_BASE                  "$OFM_PATH/comp/base/pkg"
set MI32_ASYNC_HANDSHAKE_BASE "$OFM_PATH/comp/mi_tools/async"
set MI32_PIPE_BASE            "$OFM_PATH/comp/mi_tools/pipe"
set MEMX_BASE                 "$OFM_PATH/comp/base/mem/sdp_memx"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
   [list "MI32_ASYNC_HANDSHAKE" $MI32_ASYNC_HANDSHAKE_BASE "FULL" ] \
   [list "MI32_PIPE"            $MI32_PIPE_BASE            "FULL" ] \
   [list "MEMX"                 $MEMX_BASE                 "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/ctrl_unit.vhd"
