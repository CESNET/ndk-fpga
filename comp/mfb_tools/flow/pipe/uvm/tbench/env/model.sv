//-- model.sv: Model of implementation
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): David Beneš <xbenes52@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class model #(ITEM_WIDTH, META_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_mfb_pipe::model#(ITEM_WIDTH, META_WIDTH))

    //Model I/O
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH))  data_in;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(META_WIDTH))        meta_in;
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH))      data_out;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(META_WIDTH))            meta_out;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        //MFB data
        data_in   = new("data_in",  this);
        data_out  = new("data_out", this);

        //MFB meta
        meta_in   = new("meta_in",  this);
        meta_out  = new("meta_out", this);

    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (data_in.used() != 0);
        ret |= (meta_in.used() != 0);
        return ret;
    endfunction

    task run_data();
        uvm_logic_vector_array::sequence_item #(ITEM_WIDTH) tr_mfb_data_in;

        forever begin
            data_in.get(tr_mfb_data_in);
            data_out.write(tr_mfb_data_in);
        end
    endtask

    task run_meta();
        uvm_logic_vector::sequence_item #(META_WIDTH) tr_mfb_meta_in;

        forever begin
            meta_in.get(tr_mfb_meta_in);
            meta_out.write(tr_mfb_meta_in);
        end
    endtask

    task run_phase(uvm_phase phase);
        fork
            run_data();
            if (META_WIDTH > 0) begin
                run_meta();
            end
        join_none
    endtask
endclass
