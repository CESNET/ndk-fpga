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
class sequencer#(SEGMENTS) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mac_seg_tx::sequencer#(SEGMENTS));

    // variables
    uvm_reset::sequencer                      reset_sequencer;
    uvm_logic_vector_array_mfb::sequencer_rx#(8, 1) rx_sequencer;
    uvm_intel_mac_seg::sequencer#(SEGMENTS)   tx_sequencer;

    //functions
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass


