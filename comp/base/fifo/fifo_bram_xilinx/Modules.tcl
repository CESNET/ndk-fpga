# Modules.tcl: Components include script
# Copyright (C) 2016 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set MOD "$MOD $ENTITY_BASE/fifo_bram_xilinx_ent.vhd"

global SYNTH_FLAGS
if { [info exists SYNTH_FLAGS(TOOL)] && $SYNTH_FLAGS(TOOL) == "quartus" } {
    set MOD "$MOD $ENTITY_BASE/fifo_bram_xilinx_empty.vhd"
} else {
    set MOD "$MOD $ENTITY_BASE/fifo_bram_xilinx.vhd"
    lappend SRCS(CONSTR_VIVADO) [list $ENTITY_BASE/fifo_bram_xilinx.xdc SCOPED_TO_REF FIFO_BRAM_XILINX]
}
