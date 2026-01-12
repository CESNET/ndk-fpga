//-- sequence.sv: AVST credit control sequence
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequence_down extends uvm_common::sequence_base #(config_sequence, sequence_item);
    `uvm_object_utils(uvm_crdt::sequence_down)
    `uvm_declare_p_sequencer(uvm_crdt::sequencer)

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_simple");
        super.new(name);
    endfunction

    task send_frame(int unsigned init);
        start_item(req);
        void'(req.randomize() with {init_done == init;});
        finish_item(req);
    endtask

    // ------------------------------------------------------------------------
    // Generates transactions
    task body;
        req = sequence_item::type_id::create("req");

        forever begin
            if (p_sequencer.reset_sync.has_been_reset()) begin
                send_frame(0);
                send_frame(0);
                send_frame(0);
            end else begin
                send_frame(1);
            end
        end
    endtask
endclass

class sequence_up extends uvm_common::sequence_base #(config_sequence, sequence_item);
    `uvm_object_utils(uvm_crdt::sequence_up)
    `uvm_declare_p_sequencer(uvm_crdt::sequencer)

    // ------------------------------------------------------------------------
    // Variables
    uvm_crdt::tr_planner planner;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_stop");
        super.new(name);
    endfunction

    task send_frame(int unsigned init);

        start_item(req);
        req.init_done = init;
        req.update = 0;
        if ($urandom_range(0, 20) == 0) begin
            req.update[0] = 1;
            req.cnt_ph = $urandom_range(0, planner.cnt_ph < 2**2 ? planner.cnt_ph : 2**2-1);
            planner.cnt_ph -= req.cnt_ph;
        end

        if ($urandom_range(0, 20) == 0) begin
            req.update[1] = 1;
            req.cnt_nph = $urandom_range(0, planner.cnt_nph < 2**2 ? planner.cnt_nph : 2**2-1);
            planner.cnt_nph -= req.cnt_nph;
        end

        if ($urandom_range(0, 20) == 0) begin
            req.update[2] = 1;
            req.cnt_cplh = $urandom_range(0, planner.cnt_cplh < 2**2 ? planner.cnt_cplh : 2**2-1);
            planner.cnt_cplh -= req.cnt_cplh;
        end

        if ($urandom_range(0, 20) == 0) begin
            req.update[3] = 1;
            req.cnt_pd = $urandom_range(0, planner.cnt_pd < 2**4 ? planner.cnt_pd : 2**4-1);
            planner.cnt_pd -= req.cnt_pd;
        end

        if ($urandom_range(0, 20) == 0) begin
            req.update[5] = 1;
            req.cnt_cpld = $urandom_range(0, planner.cnt_cpld < 2**4 ? planner.cnt_cpld : 2**4-1);
            planner.cnt_cpld -= req.cnt_cpld;
        end

        finish_item(req);
    endtask

    // ------------------------------------------------------------------------
    // Generates transactions
    task body;
        req = sequence_item::type_id::create("req");

        forever begin
            if (p_sequencer.reset_sync.has_been_reset()) begin
                send_frame(0);
                send_frame(0);
                send_frame(0);
            end else begin
                send_frame(1);
            end
        end
    endtask
endclass


