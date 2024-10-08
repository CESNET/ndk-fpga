// model.sv: Model of implementation
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class model #(RX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, MOD_W) extends uvm_component;
    `uvm_component_param_utils(uvm_mfb_crossbarx_stream2::model #(RX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, MOD_W))

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(RX_MFB_ITEM_W))   input_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(USERMETA_W))            input_meta;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(RX_MVB_ITEM_W))         input_mvb;
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(RX_MFB_ITEM_W))       out_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(USERMETA_W))                out_meta;

    protected int unsigned transactions;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        input_data   = new("input_data", this);
        input_meta   = new("input_meta", this);
        input_mvb    = new("input_mvb", this);
        out_data     = new("out_data", this);
        out_meta     = new("out_meta", this);
        transactions = 0;

    endfunction

    task run_phase(uvm_phase phase);

        uvm_logic_vector_array::sequence_item #(RX_MFB_ITEM_W) tr_input_data;
        uvm_logic_vector::sequence_item #(USERMETA_W)          tr_input_meta;
        uvm_logic_vector::sequence_item #(RX_MVB_ITEM_W)       tr_input_mvb;
        uvm_logic_vector_array::sequence_item #(RX_MFB_ITEM_W) tr_output_data;
        uvm_logic_vector::sequence_item #(USERMETA_W)          tr_output_meta;

        string str = "";
        logic mod_discard;
        logic mod_sof_en;
        logic mod_sof_type;
        int mod_sof_size;
        logic mod_eof_en;
        logic mod_eof_type;
        int mod_eof_size;
        int mfb_orig_size;
        int mfb_new_size;
        int mod_sof_trim;
        int mod_sof_extend;

        forever begin

            input_data.get(tr_input_data);
            //input_meta.get(tr_input_meta);
            input_mvb.get(tr_input_mvb);


            // send usermeta to output
            tr_output_meta = uvm_logic_vector::sequence_item #(USERMETA_W)::type_id::create("tr_output_meta", this);
            tr_output_meta.data = tr_input_mvb.data[USERMETA_W-1 -: USERMETA_W];
            // get mod instructions
            mod_discard  = tr_input_mvb.data[USERMETA_W];
            mod_sof_size = tr_input_mvb.data[USERMETA_W+1+MOD_W-1 -: MOD_W];
            mod_sof_en   = tr_input_mvb.data[USERMETA_W+1+MOD_W];
            mod_sof_type = tr_input_mvb.data[USERMETA_W+MOD_W+2];
            mod_eof_size = tr_input_mvb.data[USERMETA_W+MOD_W+3+MOD_W-1 -: MOD_W];
            mod_eof_en   = tr_input_mvb.data[USERMETA_W+MOD_W+3+MOD_W];
            mod_eof_type = tr_input_mvb.data[USERMETA_W+MOD_W+3+MOD_W+1];

            if (mod_sof_en == 0) begin
                mod_sof_size = 0;
            end

            if (mod_eof_en == 0) begin
                mod_eof_size = 0;
            end

            mfb_orig_size = tr_input_data.data.size();
            mod_sof_trim = 0;
            mod_sof_extend = 0;

            mfb_new_size = mfb_orig_size;
            if (mod_sof_type == 1) begin
                mfb_new_size = mfb_new_size - mod_sof_size;
            end else begin
                mfb_new_size = mfb_new_size + mod_sof_size;
            end
            if (mod_eof_type == 1) begin
                mfb_new_size = mfb_new_size - mod_eof_size;
            end else begin
                mfb_new_size = mfb_new_size + mod_eof_size;
            end

            if (mod_sof_type == 0) begin
                mod_sof_extend = mod_sof_size;
            end
            if (mod_sof_type == 1) begin
                mod_sof_trim = mod_sof_size;
            end

            tr_output_data = uvm_logic_vector_array::sequence_item #(RX_MFB_ITEM_W)::type_id::create("tr_output_data", this);
            tr_output_data.data = new[mfb_new_size];

            for (int unsigned it = 0; it < mfb_new_size; it++) begin
                if (it < mod_sof_extend || (it + mod_sof_trim) >= tr_input_data.data.size()) begin
                    tr_output_data.data[it] = 'X;
                end else begin
                    tr_output_data.data[it] = tr_input_data.data[it + mod_sof_trim - mod_sof_extend];
                end
            end
            tr_output_meta.data  = tr_input_mvb.data[USERMETA_W-1 -: USERMETA_W];
            tr_output_data.start = tr_input_mvb.start;
            tr_output_data.time_array_add(tr_input_data.start);

            if (mod_discard == 0) begin
                out_data.write(tr_output_data);
                out_meta.write(tr_output_meta);
            end

            transactions++;
            str = $sformatf( "\n======= MODEL: Transaction %0d =======", transactions);
            str = {str, $sformatf("\nDISCARD: %0b",  mod_discard)};
            str = {str, $sformatf("\nMOD SOF size: %0d",  mod_sof_size)};
            str = {str, $sformatf("\nMOD SOF type: %0b",  mod_sof_type)};
            str = {str, $sformatf("\nMOD EOF size: %0d",  mod_eof_size)};
            str = {str, $sformatf("\nMOD EOF type: %0b",  mod_eof_type)};
            str = {str, $sformatf("\nORIG size: %0d",  mfb_orig_size)};
            str = {str, $sformatf("\nNEW size: %0d",  mfb_new_size)};
            str = {str, $sformatf("\nsof_extend: %0d",  mod_sof_extend)};
            str = {str, $sformatf("\nsof_trim: %0d",  mod_sof_trim)};
            `uvm_info(this.get_full_name(), str, UVM_MEDIUM);
            `uvm_info(this.get_full_name(), tr_input_data.convert2string(), UVM_MEDIUM);
            `uvm_info(this.get_full_name(), tr_output_data.convert2string(), UVM_MEDIUM);
            `uvm_info(this.get_full_name(), tr_output_meta.convert2string(), UVM_MEDIUM);

        end

    endtask
endclass
