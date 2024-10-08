//-- model.sv: Model of implementation
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Jakub Cabal <cabal@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class model #(ITEM_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_discard::model#(ITEM_WIDTH))

    // Model inputs
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(ITEM_WIDTH+1)) model_mvb_in;

    uvm_analysis_port #(uvm_logic_vector::sequence_item #(ITEM_WIDTH)) model_mvb_out;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        model_mvb_in        = new("model_mvb_in",  this);
        model_mvb_out       = new("model_mvb_out", this);

    endfunction

    task run_phase(uvm_phase phase);

        uvm_logic_vector::sequence_item #(ITEM_WIDTH+1) tr_mvb_in;
        uvm_logic_vector::sequence_item #(ITEM_WIDTH) tr_mvb_out;

        forever begin
            logic discard;
            tr_mvb_out = uvm_logic_vector::sequence_item #(ITEM_WIDTH)::type_id::create("tr_mvb_out");

            model_mvb_in.get(tr_mvb_in);
            discard = tr_mvb_in.data[0];
            tr_mvb_out.data = tr_mvb_in.data[ITEM_WIDTH:1];

            if (discard == 1'b0) begin
                model_mvb_out.write(tr_mvb_out);
            end

        end
    endtask
endclass
