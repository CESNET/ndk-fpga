#
# Modules.tcl:
# Copyright (C) 2013 CESNET
# Author(s): Stepan Friedl <friedl@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set ETH_COMP_BASE      "$ENTITY_BASE"
set ASFIFO_BASE        "$OFM_PATH/comp/base/fifo/asfifo_bram"
set ASFIFO_XILINX_BASE "$OFM_PATH/comp/base/fifo/asfifo_bram_xilinx"
set OPEN_LOOP_BASE     "$OFM_PATH/comp/base/async/open_loop"


lappend MOD "$ETH_COMP_BASE/block_shifter.vhd"
lappend MOD "$ETH_COMP_BASE/pcs_tx_fifo.vhd"
lappend MOD "$ETH_COMP_BASE/scrambler_gen.vhd"
lappend MOD "$ETH_COMP_BASE/am_gen_4.vhd"
lappend MOD "$ETH_COMP_BASE/am_ins.vhd"
lappend MOD "$ETH_COMP_BASE/gbaser_types.vhd"
lappend MOD "$ETH_COMP_BASE/blk_enc.vhd"
lappend MOD "$ETH_COMP_BASE/gbaser_encode.vhd"

# RX modules
lappend MOD "$ETH_COMP_BASE/am_check_4.vhd"
lappend MOD "$ETH_COMP_BASE/lane_align.vhd"
lappend MOD "$ETH_COMP_BASE/ber_mon.vhd"
lappend MOD "$ETH_COMP_BASE/descrambler_gen.vhd"
lappend MOD "$ETH_COMP_BASE/pcs_rx_fifo.vhd"
lappend MOD "$ETH_COMP_BASE/gbaser_types.vhd"
lappend MOD "$ETH_COMP_BASE/blk_enc.vhd"
lappend MOD "$ETH_COMP_BASE/gbaser_encode.vhd"
lappend MOD "$ETH_COMP_BASE/blk_dec.vhd"
lappend MOD "$ETH_COMP_BASE/gbaser_decode.vhd"

lappend COMPONENTS [list "ASFIFO_BRAM"         $ASFIFO_BASE        "FULL"]
lappend COMPONENTS [list "ASFIFO_BRAM_XILINX"  $ASFIFO_XILINX_BASE "FULL"]
lappend COMPONENTS [list "ASYNC_OPEN_LOOP"     $OPEN_LOOP_BASE     "FULL"]

# Top level
lappend MOD "$ENTITY_BASE/rx_path_40g.vhd"
lappend MOD "$ENTITY_BASE/tx_path_40g.vhd"
