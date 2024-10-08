/*
 * file       : pkg.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Byte array to MII package
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef BYTE_ARRAY_MII_PKG_SV
`define BYTE_ARRAY_MII_PKG_SV
package uvm_byte_array_mii;

    typedef byte unsigned dynamic_byte_arr_t[];

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter MIN_IPG_SIZE = 5;

    `include "ipg_generator.sv"
    `include "data_buffer.sv"
    `include "channel_align.sv"
    `include "wrapper.sv"

    `include "config.sv"
    `include "ce_generator.sv"
    `include "sequencer.sv"
    `include "sequence_rx_base.sv"
    `include "sequence_rx.sv"
    `include "sequence_tx_base.sv"
    `include "sequence_tx.sv"
    `include "sequence_lib.sv"
    `include "monitor.sv"
    `include "env.sv"
endpackage

`endif
