# Modules.tcl: Local include tcl script
# Copyright (C) 2012 CESNET z. s. p. o.
# Author: Viktor Pus <pus@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set MATH_PKG  "$OFM_PATH/comp/base/pkg"

set SDP_BMEM_BASE        "$OFM_PATH/comp/base/mem/sdp_bram"
set ASFIFOX_BASE         "$OFM_PATH/comp/base/fifo/asfifox"
set ASYNC_HANDSHAKE_BASE "$OFM_PATH/comp/base/async/bus_handshake"

set COMPONENTS [list \
   [list "SDP_BMEM"        $SDP_BMEM_BASE        "FULL"] \
   [list "ASFIFOX"         $ASFIFOX_BASE         "FULL"] \
   [list "ASYNC_HANDSHAKE" $ASYNC_HANDSHAKE_BASE "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/mark_asfifo.vhd"
set MOD "$MOD $ENTITY_BASE/mfb_pd_asfifo_ent.vhd"
set MOD "$MOD $ENTITY_BASE/mfb_pd_asfifo_full.vhd"

set PACKAGES "$PACKAGES $MATH_PKG/math_pack.vhd"
set PACKAGES "$PACKAGES $MATH_PKG/type_pack.vhd"
