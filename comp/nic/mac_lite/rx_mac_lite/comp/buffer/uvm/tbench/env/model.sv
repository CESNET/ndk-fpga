// model.sv: Model of implementation
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class drop_cbs #(REGIONS) extends uvm_event_callback;
    `uvm_object_param_utils(uvm_rx_mac_lite_buffer::drop_cbs#(REGIONS))

    logic queue[$];

    function new(string name = "drop_cbs");
        super.new(name);
    endfunction

    //---------------------------------------
    // pre trigger method
    //---------------------------------------
    virtual function bit pre_trigger(uvm_event e, uvm_object data);
    endfunction

    //---------------------------------------
    // post trigger method
    //---------------------------------------
    virtual function void post_trigger(uvm_event e, uvm_object data);
        uvm_probe::data#(2*REGIONS) c_data;
        logic [REGIONS-1:0] pkt_eof;
        logic [REGIONS-1:0] pkt_drop;

        $cast(c_data, data);
        {pkt_eof, pkt_drop} = c_data.data;

        for (int unsigned it = 0; it < REGIONS; it++) begin
            if (pkt_eof[it] == 1) begin
                queue.push_back(pkt_drop[it]);
            end
        end
    endfunction

    task get(output logic drop);
        wait(queue.size() != 0);
        drop = queue.pop_front();
    endtask
endclass

class model #(MFB_ITEM_WIDTH, MFB_META_WIDTH, MFB_REGIONS, DUT_PATH) extends uvm_component;
    `uvm_component_param_utils(uvm_rx_mac_lite_buffer::model #(MFB_ITEM_WIDTH, MFB_META_WIDTH, MFB_REGIONS, DUT_PATH))

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) input_mfb_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH))       input_mfb_meta;
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))     out_mfb_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH))           out_mvb_data;

    // Protected variable
    protected drop_cbs#(MFB_REGIONS) drop_sync;
    protected logic pkt_drop[$];
    protected int unsigned pkt_cnt;
    protected int unsigned meta_cnt;
    protected int unsigned drop_cnt;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        input_mfb_data = new("input_mfb_data", this);
        input_mfb_meta = new("input_mfb_meta", this);
        out_mfb_data   = new("out_mfb_data", this);
        out_mvb_data   = new("out_mvb_data", this);

        pkt_cnt  = 0;
        meta_cnt = 0;
        drop_cnt = 0;
    endfunction

    function void build_phase(uvm_phase phase);
        drop_sync = drop_cbs#(MFB_REGIONS)::type_id::create("drop_sync", this);
    endfunction

    function string info();
        string msg = "";

        msg = {msg, $sformatf("\n\tProcessed packets %0d/%0d dropped packets %0d/%0d", (pkt_cnt - drop_cnt), pkt_cnt, drop_cnt, pkt_cnt)};
        return msg;
    endfunction


    function void connect_phase(uvm_phase phase);
        uvm_probe::pool::get_global_pool().get({"probe_event_component_", DUT_PATH, ".probe_drop"}).add_callback(drop_sync);
    endfunction

    task run_meta();
       uvm_logic_vector::sequence_item #(MFB_META_WIDTH) tr_input;

        forever begin
            logic err;
            logic force_drop;
            logic drop;

            input_mfb_meta.get(tr_input);

            err = 0;
            drop_sync.get(force_drop);
            drop = err | force_drop;

            meta_cnt++;
            `uvm_info(this.get_full_name(), $sformatf("\n\tPacket %0d drop %b error %0d\n%s", meta_cnt, drop, err, tr_input.convert2string()), UVM_HIGH);

            pkt_drop.push_back(drop);
            if (drop == 0) begin
                out_mvb_data.write(tr_input);
            end else begin
                drop_cnt++;
            end
        end
    endtask

    task run_data();
        uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) tr_input;

        forever begin
            logic drop;

            input_mfb_data.get(tr_input);
            wait(pkt_drop.size() != 0);
            drop = pkt_drop.pop_front();

            pkt_cnt++;
            `uvm_info(this.get_full_name(), $sformatf("\n\tPacket %0d drop %b\n%s", pkt_cnt, drop, tr_input.convert2string()), UVM_HIGH);
            if (drop == 0) begin
                out_mfb_data.write(tr_input);
            end
        end
    endtask

    task run_phase(uvm_phase phase);
        fork
            run_meta();
            run_data();
        join
    endtask
endclass
