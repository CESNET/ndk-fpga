// model.sv: Model of implementation
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class model #(RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH) extends uvm_component;
    `uvm_component_param_utils(merge_items::model #(RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH))

    // Model inputs
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(RX0_ITEM_WIDTH)) model_mvb_in0;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(RX1_ITEM_WIDTH)) model_mvb_in1;

    // Model outputs
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(TX_ITEM_WIDTH)) model_mvb_out;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        model_mvb_in0 = new("model_mvb_in0", this);
        model_mvb_in1 = new("model_mvb_in1", this);
        model_mvb_out = new("model_mvb_out", this);

    endfunction

    task run_phase(uvm_phase phase);
        uvm_logic_vector::sequence_item #(RX0_ITEM_WIDTH) tr_mvb_in0;
        uvm_logic_vector::sequence_item #(RX1_ITEM_WIDTH) tr_mvb_in1;
        uvm_logic_vector::sequence_item #(TX_ITEM_WIDTH)  tr_mvb_out;

        forever begin
            model_mvb_in0.get(tr_mvb_in0);
            model_mvb_in1.get(tr_mvb_in1);

            tr_mvb_out = uvm_logic_vector::sequence_item #(TX_ITEM_WIDTH)::type_id::create("tr_mvb_out_item");

            tr_mvb_out.data = { tr_mvb_in1.data, tr_mvb_in0.data };
            tr_mvb_out.time_array_add(tr_mvb_in0.start);
            tr_mvb_out.time_array_add(tr_mvb_in1.start);

            model_mvb_out.write(tr_mvb_out);

        end

    endtask

endclass
