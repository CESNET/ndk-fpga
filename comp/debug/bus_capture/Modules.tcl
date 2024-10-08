# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set PKG_BASE                  "$OFM_PATH/comp/base/pkg"
set SDP_MEMX_BASE             "$OFM_PATH/comp/base/mem/sdp_memx"
set GEN_MUX_BASE              "$OFM_PATH/comp/base/logic/mux"
set MI32_ASYNC_HANDSHAKE_BASE "$OFM_PATH/comp/mi_tools/async"
set MI32_PIPE_BASE            "$OFM_PATH/comp/mi_tools/pipe"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
    [ list "MI32_ASYNC_HANDSHAKE" $MI32_ASYNC_HANDSHAKE_BASE "FULL" ] \
    [ list "MI32_PIPE"            $MI32_PIPE_BASE            "FULL" ] \
    [ list "SDP_MEMX"             $SDP_MEMX_BASE             "FULL" ] \
    [ list "GEN_MUX"              $GEN_MUX_BASE              "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/bus_capture.vhd"
set MOD "$MOD $ENTITY_BASE/bus_capture_mi.vhd"
