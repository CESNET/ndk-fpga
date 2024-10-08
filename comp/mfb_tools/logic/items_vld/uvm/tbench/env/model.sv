// model.sv: Model of implementation
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class model #(META_WIDTH, MVB_DATA_WIDTH, MFB_ITEM_WIDTH, OFFSET_WIDTH, LENGTH_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_items_valid::model #(META_WIDTH, MVB_DATA_WIDTH, MFB_ITEM_WIDTH, OFFSET_WIDTH, LENGTH_WIDTH))

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) input_mfb;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(META_WIDTH))           input_meta;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(MVB_DATA_WIDTH))           out_mvb;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(1))                        out_mvb_end;

    typedef logic [MVB_DATA_WIDTH-1 : 0] mvb_fifo[$];
    int unsigned                         pkt_cnt;
    int unsigned                         out_cnt;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        input_mfb     = new("input_mfb", this);
        input_meta    = new("input_meta", this);
        out_mvb       = new("out_mvb", this);
        out_mvb_end = new("out_mvb_end", this);
        pkt_cnt = 0;
        out_cnt = 0;
    endfunction

    task extract_valid_data(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) frame, int unsigned offset, int unsigned length);
        uvm_logic_vector::sequence_item #(MVB_DATA_WIDTH) out_mvb_tr;
        uvm_logic_vector::sequence_item #(1)              out_mvb_end_tr;
        string msg = "";

        msg = {msg, $sformatf("\n\tMFB PKT COUNT %d",  pkt_cnt)};
        `uvm_info(this.get_full_name(), msg ,UVM_FULL)

        for (int unsigned it = offset; it < offset+length; it++) begin
            out_cnt++;

            out_mvb_tr       = uvm_logic_vector::sequence_item #(MVB_DATA_WIDTH)::type_id::create("out_mvb_tr");
            out_mvb_tr.data  = frame.data[it];
            `uvm_info(this.get_full_name(), out_mvb_tr.convert2string() ,UVM_MEDIUM)

            out_mvb_end_tr = uvm_logic_vector::sequence_item #(1)::type_id::create("out_mvb_end_tr");
            if (it < offset+length-1) begin
                out_mvb_end_tr.data = 1'b0;
            end else begin
                out_mvb_end_tr.data = 1'b1;
            end

            out_mvb_end.write(out_mvb_end_tr);
            out_mvb.write(out_mvb_tr);
        end
    endtask

    task run_phase(uvm_phase phase);

        uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) tr_input_mfb;
        uvm_logic_vector::sequence_item #(META_WIDTH)           tr_input_meta;
        uvm_logic_vector::sequence_item #(1)                    chsum_en;

        logic [OFFSET_WIDTH-1 : 0] offset = '0;
        logic [LENGTH_WIDTH-1 : 0] length = '0;
        logic                      enable = '0;

        forever begin

            string msg = "";

            input_mfb.get(tr_input_mfb);
            input_meta.get(tr_input_meta);

            pkt_cnt++;
            `uvm_info(this.get_full_name(), tr_input_mfb.convert2string() ,UVM_FULL)
            `uvm_info(this.get_full_name(), tr_input_meta.convert2string() ,UVM_FULL) // useless

            {enable, length, offset} = tr_input_meta.data[OFFSET_WIDTH+LENGTH_WIDTH : 0];
            msg = $sformatf( "\n%s\nOFFSET %d\n", msg, offset);
            msg = $sformatf( "\n%sLENGTH %d\n", msg, length);
            msg = $sformatf( "\n%sENABLE %d\n", msg, enable);
            `uvm_info(this.get_full_name(), msg ,UVM_HIGH)
            if (enable) begin
                extract_valid_data(tr_input_mfb, offset, length);
            end

        end

    endtask
endclass
