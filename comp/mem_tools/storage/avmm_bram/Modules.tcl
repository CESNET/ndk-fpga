# Modules.tcl: Script to include sources
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SDP_BRAM_BASE "$OFM_PATH/comp/base/mem/sdp_bram"

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [list "SDP_BRAM" $SDP_BRAM_BASE "FULL" ]

lappend MOD "$ENTITY_BASE/avmm_bram.vhd"
