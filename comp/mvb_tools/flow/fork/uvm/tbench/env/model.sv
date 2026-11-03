// model.sv: Model of implementation
// MVB_FORK UVM verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
//
// The fork replicates every input item to all OUTPUT_PORTS output streams.
// The model simply copies each received transaction to every output port.
//
// SPDX-License-Identifier: BSD-3-Clause


class model #(ITEM_WIDTH, OUTPUT_PORTS) extends uvm_component;
    `uvm_component_param_utils(uvm_mvb_fork::model#(ITEM_WIDTH, OUTPUT_PORTS))

    // Model input
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(ITEM_WIDTH)) model_mvb_in;

    // Model outputs, one per fork output port
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(ITEM_WIDTH)) model_mvb_out [OUTPUT_PORTS-1 : 0];

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        model_mvb_in = new("model_mvb_in", this);
        for (int i = 0; i < OUTPUT_PORTS; i++) begin
            model_mvb_out[i] = new($sformatf("model_mvb_out_%0d", i), this);
        end
    endfunction

    task run_phase(uvm_phase phase);

        uvm_logic_vector::sequence_item #(ITEM_WIDTH) tr_mvb_in;
        uvm_logic_vector::sequence_item #(ITEM_WIDTH) tr_mvb_out;

        forever begin

            // Gets the input transaction
            model_mvb_in.get(tr_mvb_in);

            // Replicates the transaction to every output port
            for (int i = 0; i < OUTPUT_PORTS; i++) begin
                tr_mvb_out = uvm_logic_vector::sequence_item #(ITEM_WIDTH)::type_id::create("tr_mvb_out");
                tr_mvb_out.data         = tr_mvb_in.data;
                tr_mvb_out.time_array_add(tr_mvb_in.start);
                tr_mvb_out.set_transaction_id(tr_mvb_in.get_transaction_id());
                model_mvb_out[i].write(tr_mvb_out);
            end

        end

    endtask

endclass
