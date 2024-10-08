// model.sv: Model of implementation
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Mikuláš Brázda <xbrazd21@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class model#(ITEM_WIDTH, META_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_mfb_fifox::model#(ITEM_WIDTH, META_WIDTH))

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))   input_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(META_WIDTH))   input_meta;

    uvm_analysis_port #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))       out_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(META_WIDTH))   out_meta;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        input_data    = new("input_data", this);
        input_meta    = new("input_meta", this);
        out_data      = new("out_data", this);
        out_meta      = new("out_meta", this);

    endfunction


    task run_phase(uvm_phase phase);

        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) tr_input_packet;
        uvm_logic_vector::sequence_item#(META_WIDTH) tr_input_meta;
        forever begin
            input_data.get(tr_input_packet);
            input_meta.get(tr_input_meta);
            out_data.write(tr_input_packet);
            out_meta.write(tr_input_meta);
        end
    endtask
endclass
