# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set MOD "$MOD $ENTITY_BASE/sdp_bram_xilinx_ent.vhd"

global SYNTH_FLAGS
if { [info exists SYNTH_FLAGS(TOOL)] && $SYNTH_FLAGS(TOOL) != "vivado" } {
    set MOD "$MOD $ENTITY_BASE/sdp_bram_xilinx_empty.vhd"
} else {
    set MOD "$MOD $ENTITY_BASE/sdp_bram_xilinx.vhd"
}
