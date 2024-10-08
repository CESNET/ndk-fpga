# Modules.tcl: Script to compile single module
# Copyright (C) 2022 CESNET
# Author: Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set GEN_LUTRAM_BASE  "$OFM_PATH/comp/base/mem/gen_lutram"
set SDP_BRAM_BE_BASE "$OFM_PATH/comp/base/mem/sdp_bram"

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [list "GEN_LUTRAM"  $GEN_LUTRAM_BASE  "FULL" ]
lappend COMPONENTS [list "SDP_BRAM_BE" $SDP_BRAM_BE_BASE "FULL" ]

lappend MOD "$ENTITY_BASE/mvb_lut_lutram.vhd"
lappend MOD "$ENTITY_BASE/mvb_lut_bram.vhd"
lappend MOD "$ENTITY_BASE/mvb_lut.vhd"
