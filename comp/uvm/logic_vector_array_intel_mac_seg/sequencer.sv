/*
 * file       : sequencer.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: convert byte array to intel mac seq sequencer
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequencer extends uvm_sequencer;
    `uvm_component_utils(uvm_logic_vector_array_intel_mac_seg::sequencer)
    localparam LOGIC_WIDTH = 6;
    localparam ITEM_WIDTH  = 8;

    uvm_logic_vector_array::sequencer#(ITEM_WIDTH)     m_packet;
    uvm_logic_vector::sequencer#(LOGIC_WIDTH)          m_error;

    logic ready[$];

    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
        ready = {0};
    endfunction
endclass
