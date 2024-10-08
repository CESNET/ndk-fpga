// model.sv: Model of implementation
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kondys <kondys@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class model #(MFB_REGIONS, MFB_ITEM_WIDTH, MFB_META_WIDTH) extends uvm_component;
    `uvm_component_param_utils(frame_masker::model #(MFB_REGIONS, MFB_ITEM_WIDTH, MFB_META_WIDTH))

    localparam string DUT_PATH = "testbench.DUT_U.VHDL_DUT_U";

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) input_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH))       input_meta;
    uvm_analysis_port     #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) out_data;
    uvm_analysis_port     #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH))       out_meta;

    protected frame_masker::probe_cbs#(MFB_REGIONS)                                                            discards;


    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        input_data = new("input_data", this);
        input_meta = new("input_meta", this);
        out_data   = new("out_data",   this);
        out_meta   = new("out_meta",   this);

    endfunction


    function void connect_phase(uvm_phase phase);
        discards = frame_masker::probe_cbs#(MFB_REGIONS)::type_id::create("discards", this);
        //register
        uvm_probe::pool::get_global_pool().get({"probe_event_component_", DUT_PATH, ".probe_mask2discard"}).add_callback(discards);
    endfunction


    task run_mask_packets();
        uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) input_data_tr;
        logic                                                   discard;

        forever begin

            string msg = "\n";

            discards.get_discard_data(discard);
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

            discards.get_discard_meta(discard);
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
