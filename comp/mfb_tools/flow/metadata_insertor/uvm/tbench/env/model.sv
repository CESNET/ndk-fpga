// model.sv: Model of implementation
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class model #(MFB_ITEM_WIDTH, MVB_ITEM_WIDTH, MFB_META_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_metadata_insertor::model #(MFB_ITEM_WIDTH, MVB_ITEM_WIDTH, MFB_META_WIDTH))

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))      input_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH))            input_meta;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH))            input_mvb;
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))          out_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH+MVB_ITEM_WIDTH)) out_meta;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        input_data = new("input_data", this);
        input_meta = new("input_meta", this);
        input_mvb  = new("input_mvb", this);
        out_data   = new("out_data", this);
        out_meta   = new("out_meta", this);

    endfunction

    task run_phase(uvm_phase phase);

        uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)          tr_input_data;
        uvm_logic_vector::sequence_item #(MFB_META_WIDTH)                tr_input_meta;
        uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH)                tr_input_mvb;
        uvm_logic_vector::sequence_item #(MFB_META_WIDTH+MVB_ITEM_WIDTH) tr_output_meta;

        forever begin

            input_data.get(tr_input_data);
            input_meta.get(tr_input_meta);
            input_mvb.get(tr_input_mvb);

            tr_output_meta = uvm_logic_vector::sequence_item #(MFB_META_WIDTH+MVB_ITEM_WIDTH)::type_id::create("tr_output_data_item");

            tr_output_meta.data = {tr_input_meta.data, tr_input_mvb.data};
            tr_output_meta.time_array_add(tr_input_meta.start);
            tr_output_meta.time_array_add(tr_input_mvb.start);

            out_data.write(tr_input_data);
            out_meta.write(tr_output_meta);

        end

    endtask
endclass
