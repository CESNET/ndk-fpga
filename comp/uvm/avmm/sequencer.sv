// sequencer.sv: AVMM sequencer
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Slave
class sequencer_slave #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_sequencer #(sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH), sequence_item_response #(DATA_WIDTH));
    `uvm_component_param_utils(uvm_avmm::sequencer_slave #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // Constructor
    function new(string name = "sequencer_slave", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass

// Master
class sequencer_master #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_sequencer #(sequence_item_response #(DATA_WIDTH), sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH));
    `uvm_component_param_utils(uvm_avmm::sequencer_master #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // Shared response input fifo
    uvm_tlm_analysis_fifo #(response_item #(DATA_WIDTH)) response_in;

    // Reset
    uvm_reset::sync_terminate reset_sync;

    // Constructor
    function new(string name = "sequencer_master", uvm_component parent = null);
        super.new(name, parent);

        reset_sync  = new();
        response_in = new("response_in", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        uvm_config_db #(uvm_tlm_analysis_fifo #(response_item #(DATA_WIDTH)))::set(this, "", "response_in", response_in);
    endfunction

    task run_phase(uvm_phase phase);
        run_reseter();
    endtask

    // Reset logic
    task run_reseter();
        forever begin
            wait(reset_sync.has_been_reset());
            response_in.flush();
            wait(!reset_sync.is_reset());
        end
    endtask

endclass
