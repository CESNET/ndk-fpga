// model.sv: Model of implementation
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kondys <kondys@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class model #(MFB_REGIONS, MFB_ITEM_WIDTH, MFB_META_WIDTH) extends uvm_component;
    `uvm_component_param_utils(frame_masker::model #(MFB_REGIONS, MFB_ITEM_WIDTH, MFB_META_WIDTH))

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) input_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH))       input_meta;
    uvm_tlm_analysis_fifo #(bit)                                                     input_data_discard;
    uvm_tlm_analysis_fifo #(bit)                                                     input_meta_discard;
    uvm_analysis_port     #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) out_data;
    uvm_analysis_port     #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH))       out_meta;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        input_data         = new("input_data", this);
        input_meta         = new("input_meta", this);
        input_data_discard = new("input_data_discard", this);
        input_meta_discard = new("input_meta_discard", this);
        out_data           = new("out_data",   this);
        out_meta           = new("out_meta",   this);

    endfunction

    task run_mask_packets();
        uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) input_data_tr;
        logic                                                   discard;

        forever begin

            string msg = "\n";

            input_data_discard.get(discard);
            input_data.get(input_data_tr);

            msg = {msg, " Processing packet:\n"};
            msg = {msg, input_data_tr.convert2string(), "\n"};

            if (MFB_REGIONS > 1) begin
                if (discard == 0) begin
                    out_data.write(input_data_tr);
                    msg = {msg, $sformatf(" Packet WAS NOT discarded!\n")};
                end else begin
                    msg = {msg, $sformatf(" Packet WAS discarded!\n")};
                end
            end else begin
                out_data.write(input_data_tr);
            end

            `uvm_info(get_type_name(), msg, UVM_HIGH)
        end

    endtask


    task run_mask_meta();
        uvm_logic_vector::sequence_item #(MFB_META_WIDTH) input_meta_tr;
        logic                                             discard;

        forever begin

            string msg = "\n";

            input_meta_discard.get(discard);
            input_meta.get(input_meta_tr);

            msg = {msg, " Packet's metadata:\n"};
            msg = {msg, input_meta_tr.convert2string(), "\n"};

            if (MFB_REGIONS > 1) begin
                if (discard == 0) begin
                    out_meta.write(input_meta_tr);
                    msg = {msg, " Packet WAS NOT discarded!\n"};
                    // $write(msg, "%s INPUT META\n", msg);
                    // msg = {msg, $sformatf(" %s\n",  input_meta_tr.convert2string())};
                    // `uvm_info(get_type_name(), msg, UVM_NONE)
                end else begin
                    msg = {msg, " Packet WAS discarded!\n"};
                end
            end else begin
                out_meta.write(input_meta_tr);
            end

            `uvm_info(get_type_name(), msg, UVM_HIGH)
        end

    endtask

    task run_phase(uvm_phase phase);

    fork
        run_mask_packets();
        run_mask_meta();
    join_none;

    endtask
endclass
