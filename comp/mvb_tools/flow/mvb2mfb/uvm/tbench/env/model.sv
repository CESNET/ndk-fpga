// model.sv: Model of implementation
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class model #(MFB_ITEM_WIDTH, MVB_ITEM_WIDTH, MFB_META_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_mvb2mfb::model #(MFB_ITEM_WIDTH, MVB_ITEM_WIDTH, MFB_META_WIDTH))

    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH))            input_mvb;
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))          out_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH)) out_meta;

    localparam MVB_ITEM_WIDTH_RAW = MVB_ITEM_WIDTH - MFB_META_WIDTH;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        input_mvb  = new("input_mvb", this);
        out_data   = new("out_data", this);
        out_meta   = new("out_meta", this);

    endfunction

    task run_phase(uvm_phase phase);

        uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH)                tr_input_mvb;
        uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)          tr_output_data;
        uvm_logic_vector::sequence_item #(MFB_META_WIDTH) tr_output_meta;
        logic [MFB_META_WIDTH-1:0]     mvb_meta;
        logic [MVB_ITEM_WIDTH_RAW-1:0] mvb_data;

        forever begin
            input_mvb.get(tr_input_mvb);

            tr_output_data = uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)::type_id::create("tr_output_data_item");
            tr_output_meta = uvm_logic_vector::sequence_item #(MFB_META_WIDTH)::type_id::create("tr_output_data_item");

            mvb_data = tr_input_mvb.data[MVB_ITEM_WIDTH_RAW-1:0];
            mvb_meta = tr_input_mvb.data[MVB_ITEM_WIDTH-1:MVB_ITEM_WIDTH_RAW];

            tr_output_data.data = {<<byte{mvb_data}};
            tr_output_data.time_array_add(tr_input_mvb.start);

            tr_output_meta.data = mvb_meta;
            tr_output_meta.time_array_add(tr_input_mvb.start);

            out_data.write(tr_output_data);
            out_meta.write(tr_output_meta);

        end

    endtask
endclass
