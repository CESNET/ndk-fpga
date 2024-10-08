// model.sv: Model of implementation
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class ts_limiter_item#(MFB_ITEM_WIDTH, TIMESTAMP_WIDTH) extends uvm_common::sequence_item;

    logic [TIMESTAMP_WIDTH-1 : 0]                           timestamp;
    uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) data_tr;

    function string convert2string();
        string msg;

        msg = $sformatf( "\n\ttimestamp %0d", timestamp);
        return msg;
    endfunction

endclass


class model #(MFB_ITEM_WIDTH, RX_MFB_META_WIDTH, TX_MFB_META_WIDTH, TIMESTAMP_WIDTH, QUEUES, TIMESTAMP_FORMAT) extends uvm_component;
    `uvm_component_param_utils(uvm_timestamp_limiter::model #(MFB_ITEM_WIDTH, RX_MFB_META_WIDTH, TX_MFB_META_WIDTH, TIMESTAMP_WIDTH, QUEUES, TIMESTAMP_FORMAT))

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))              input_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(RX_MFB_META_WIDTH))                 input_meta;
    uvm_analysis_port #(uvm_timestamp_limiter::ts_limiter_item#(MFB_ITEM_WIDTH, TIMESTAMP_WIDTH)) out_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(TX_MFB_META_WIDTH))                     out_meta;


    protected uvm_logic_vector::sequence_item #(RX_MFB_META_WIDTH) header[$];

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        input_data = new("input_data", this);
        input_meta = new("input_meta", this);
        out_data   = new("out_data", this);
        out_meta   = new("out_meta", this);

    endfunction

    task run_meta(uvm_phase phase);
        uvm_logic_vector::sequence_item #(RX_MFB_META_WIDTH) tr_input_meta;
        uvm_logic_vector::sequence_item #(TX_MFB_META_WIDTH) tr_output_meta;
        string msg;

        forever begin
            input_meta.get(tr_input_meta);

            msg = "";
            msg = {msg, $sformatf(" INPUT TS %h\n",  tr_input_meta.data[TIMESTAMP_WIDTH-1 : 0])};
            msg = {msg, $sformatf(" INPUT META %h\n",  tr_input_meta.data[RX_MFB_META_WIDTH-1 : TIMESTAMP_WIDTH+$clog2(QUEUES)])};
            msg = {msg, $sformatf(" %s\n",  tr_input_meta.convert2string())};

            tr_output_meta = uvm_logic_vector::sequence_item #(TX_MFB_META_WIDTH)::type_id::create("tr_output_data_item");
            tr_output_meta.time_array_add(tr_input_meta.start);

            tr_output_meta.data = tr_input_meta.data[RX_MFB_META_WIDTH-1 : TIMESTAMP_WIDTH+$clog2(QUEUES)];
            msg = {msg, $sformatf(" OUTPUT META\n")};
            msg = {msg, $sformatf(" %s\n",  tr_output_meta.convert2string())};
            `uvm_info(get_type_name(), msg, UVM_MEDIUM)

            tr_output_meta.tag = "TS_LIMITER_META";

            header.push_back(tr_input_meta);
            if (TX_MFB_META_WIDTH > 0) begin
                out_meta.write(tr_output_meta);
            end
        end
    endtask

    task run_data(uvm_phase phase);
        uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)                  tr_input_data;
        uvm_logic_vector::sequence_item #(RX_MFB_META_WIDTH)                     tr_input_meta;
        uvm_timestamp_limiter::ts_limiter_item#(MFB_ITEM_WIDTH, TIMESTAMP_WIDTH) tr_output_data;
        logic [TIMESTAMP_WIDTH-1 : 0] prev_ts = 0;

        forever begin
            logic [$clog2(QUEUES)-1 : 0] mfb_queue = '0;
            string msg = "\n";
            string queue_str = "";

            input_data.get(tr_input_data);
            wait(header.size() != 0);
            tr_input_meta = header.pop_front();


            tr_output_data = new();

            msg = {msg, $sformatf(" INPUT DATA\n")};
            msg = {msg, $sformatf(" %s\n",  tr_input_data.convert2string())};

            tr_output_data.time_array_add(tr_input_data.start);
            tr_output_data.time_array_add(tr_input_meta.start);

            tr_output_data.data_tr = tr_input_data;
            if (TIMESTAMP_FORMAT == 0) begin
                tr_output_data.timestamp = tr_input_meta.data[TIMESTAMP_WIDTH-1 : 0];
            end else begin
                tr_output_data.timestamp = tr_input_meta.data[TIMESTAMP_WIDTH-1 : 0] - prev_ts;
                prev_ts = tr_input_meta.data[TIMESTAMP_WIDTH-1 : 0];
            end

            if (QUEUES != 1) begin
                mfb_queue = tr_input_meta.data[TIMESTAMP_WIDTH+$clog2(QUEUES)-1 : TIMESTAMP_WIDTH];
                msg = {msg, $sformatf(" INPUT QUEUE %d\n",  mfb_queue)};
            end

            queue_str.itoa(int'(mfb_queue));
            tr_output_data.tag = {"TS_LIMITER_DATA_", queue_str};

            out_data.write(tr_output_data);

        end
    endtask


    task run_phase(uvm_phase phase);
        fork
            run_meta(phase);
            run_data(phase);
        join
    endtask
endclass
