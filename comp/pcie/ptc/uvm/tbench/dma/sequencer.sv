// sequencer.sv :
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class seq_info;

    logic tags[int unsigned][logic [8-1:0]];

    function new();
        tags.delete();
    endfunction

    function void requester_remove(int unsigned unit_id);
        tags.delete(unit_id);
    endfunction

    function void tag_add(int unsigned unit_id, logic [8-1:0] tag);
        tags[unit_id][tag] = 1;
    endfunction

    function void tag_remove(int unsigned unit_id, logic [8-1:0] tag);
        if (tags.exists(unit_id)) begin
            tags[unit_id].delete(tag);
            if (tags[unit_id].size() == 0) begin
                tags.delete(unit_id);
            end
        end else begin
            const int unsigned indexes[] = tags.find_index() with (1);
            string msg;

            msg = "{";
            foreach(indexes[it]) begin
                msg = {msg, $sformatf(" 0x%0h", indexes[it])};
            end
            msg = {msg, "}"};
            `uvm_warning("seq_info", $sformatf("\n\tUnknown unitid 0x%h\n\t%s", unit_id, msg));
        end
    endfunction
endclass


//typedef uvm_sequencer#(sequence_item_rq) sequencer;

class sequencer extends uvm_sequencer #(sequence_item_rq);
    `uvm_component_param_utils(uvm_dma::sequencer)

    uvm_reset::sync_terminate reset_sync;

    //responses
    uvm_tlm_analysis_fifo #(uvm_dma::sequence_item_rc) fifo_rsp;
    seq_info info;

    // Constructor
    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
        reset_sync = new();
        fifo_rsp   = new("fifo_rsp", this);
        info       = new();
    endfunction: new

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        uvm_config_db #(seq_info)::set(this, "", "info", info);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_dma::sequence_item_rc resp;

        forever begin
            fifo_rsp.get(resp);
            if (resp.completed == 1) begin
                info.tag_remove(resp.unit_id, resp.tag);
            end
        end
    endtask
endclass


