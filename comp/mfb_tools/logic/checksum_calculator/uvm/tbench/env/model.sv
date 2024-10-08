// model.sv: Model of implementation
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class chsum_calc_item#(MVB_DATA_WIDTH, MFB_META_WIDTH) extends uvm_common::sequence_item;

    logic                      bypass;
    logic [MFB_META_WIDTH-1:0] meta;
    logic [MVB_DATA_WIDTH-1:0] data;

    function string convert2string();
        string msg;

        msg = super.convert2string();
        msg = {msg, $sformatf("\n\tbypass %b",  bypass)};
        msg = {msg, $sformatf("\n\tmeta   %h",  meta)};
        msg = {msg, $sformatf("\n\tdata   %h",  data)};
        return msg;
    endfunction

endclass


class model #(META_WIDTH, MVB_DATA_WIDTH, MFB_ITEM_WIDTH, OFFSET_WIDTH, LENGTH_WIDTH, VERBOSITY, MFB_META_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_checksum_calculator::model #(META_WIDTH, MVB_DATA_WIDTH, MFB_ITEM_WIDTH, OFFSET_WIDTH, LENGTH_WIDTH, VERBOSITY, MFB_META_WIDTH))

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) input_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(META_WIDTH))           input_meta;
    uvm_analysis_port #(chsum_calc_item#(MVB_DATA_WIDTH, MFB_META_WIDTH))        out_checksum;
    protected int unsigned pkt_cnt;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        out_checksum = new("out_checksum", this);
        input_data   = new("input_data", this);
        input_meta   = new("input_meta", this);

        pkt_cnt = 0;
    endfunction

    function logic[16-1 : 0] checksum_calc(logic [MFB_ITEM_WIDTH-1:0] frame[], logic [OFFSET_WIDTH-1 : 0] offset, logic [LENGTH_WIDTH-1 : 0] length);
        const logic [16-1 : 0] CHCKS_MAX = '1;
        logic [16-1 : 0] ret;
        int unsigned     data_index = 0;
        logic [32-1 : 0] checksum = '0;
        int unsigned it;


        for (it = offset; (it+2) < offset+length; it +=2) begin
            checksum += {frame[it], frame[it+1]};
        end

        if (length%2 == 1) begin
            checksum += {frame[it], 8'b0};
        end else begin
            checksum += {frame[it], frame[it+1]};
        end

        while (checksum > CHCKS_MAX) begin
            checksum = checksum[15 : 0] + checksum[31 : 16];
        end;
        ret = ~(checksum[15 : 0] + checksum[31 : 16]);

        return ret;
    endfunction

    task run_phase(uvm_phase phase);

        uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) tr_input_mfb;
        uvm_logic_vector::sequence_item #(META_WIDTH)           tr_input_meta;
        chsum_calc_item#(MVB_DATA_WIDTH, MFB_META_WIDTH)        tr_out_chsum;
        logic chsum_en;

        logic [OFFSET_WIDTH-1 : 0] offset = '0;
        logic [LENGTH_WIDTH-1 : 0] length = '0;

        forever begin

            input_data.get(tr_input_mfb);
            input_meta.get(tr_input_meta);

            pkt_cnt++;
            if (VERBOSITY >= 1) begin
                `uvm_info(this.get_full_name(), tr_input_meta.convert2string() ,UVM_NONE)
                `uvm_info(this.get_full_name(), tr_input_mfb.convert2string() ,UVM_NONE)
            end

            tr_out_chsum  = new;
            tr_out_chsum.set_transaction_id(pkt_cnt);
            tr_out_chsum.time_array_add(tr_input_mfb.start);
            tr_out_chsum.time_array_add(tr_input_meta.start);

            //{chsum_en, length, offset} = tr_input_meta.data;
            offset   = tr_input_meta.data[OFFSET_WIDTH-1  : 0];
            length   = tr_input_meta.data[OFFSET_WIDTH+LENGTH_WIDTH-1  : OFFSET_WIDTH];
            chsum_en = tr_input_meta.data[OFFSET_WIDTH+LENGTH_WIDTH+1-1  : OFFSET_WIDTH+LENGTH_WIDTH];

            tr_out_chsum.meta = tr_input_meta.data[META_WIDTH-1  : OFFSET_WIDTH+LENGTH_WIDTH+1];
            tr_out_chsum.data = checksum_calc(tr_input_mfb.data, offset, length);
            tr_out_chsum.bypass    = !chsum_en;

            if (VERBOSITY >= 1) begin
                `uvm_info(this.get_full_name(), tr_out_chsum.convert2string() ,UVM_NONE)
            end

            out_checksum.write(tr_out_chsum);
        end

    endtask
endclass
