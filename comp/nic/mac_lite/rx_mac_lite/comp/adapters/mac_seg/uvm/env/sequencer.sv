/*
 * file       : sequencer.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: seqeuncer test
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


////////////////////////////////////////////////////////////////////////////////
// vurtual sequencer.
class sequencer extends uvm_sequencer;
    `uvm_component_utils(uvm_mac_seg_rx::sequencer);

    localparam LOGIC_WIDTH = 6;

    // variables
    uvm_reset::sequencer                      reset;
    uvm_logic_vector_array::sequencer#(8)     rx_packet;
    uvm_logic_vector::sequencer#(LOGIC_WIDTH) rx_error;

    //functions
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass


