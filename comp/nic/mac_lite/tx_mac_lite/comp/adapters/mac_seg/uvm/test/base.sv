/*
 * file       : base.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: base test
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class base extends uvm_test;
    `uvm_component_utils(test::base);

    /////////////////////
    // variables
    uvm_mac_seg_tx::env#(SEGMENTS, REGIONS, REGION_SIZE) m_env;

    /////////////////////
    // functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_mac_seg_tx::env#(SEGMENTS, REGIONS, REGION_SIZE)::type_id::create("m_env", this);
    endfunction

    //run virtual sequence on virtual sequencer
    virtual task run_phase(uvm_phase phase);
        uvm_mac_seg_tx::sequence_simple_1#(SEGMENTS) seq;

        phase.raise_objection(this);

        seq = uvm_mac_seg_tx::sequence_simple_1#(SEGMENTS)::type_id::create("seq");
        seq.seq_create();
        seq.randomize();
        seq.start(m_env.m_sequencer);


        #(100ns); // wait to get all data
        phase.drop_objection(this);
    endtask

endclass

