//-- monitor.sv: Monitor for MFB environment
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class monitor_logic_vector_array #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH, int unsigned READY_LATENCY) extends uvm_logic_vector_array::monitor #(ITEM_WIDTH);
    `uvm_component_param_utils(uvm_logic_vector_array_avst::monitor_logic_vector_array #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY))

    // Analysis port
    typedef monitor_logic_vector_array #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY) this_type;
    uvm_analysis_imp #(uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH), this_type) analysis_export;

    localparam EMPTY_WIDTH = $clog2(REGION_SIZE * BLOCK_SIZE);

    uvm_reset::sync_terminate                                 reset_sync;
    local uvm_logic_vector_array::sequence_item #(ITEM_WIDTH) hi_tr;
    local logic [ITEM_WIDTH-1 : 0]                            data[$];

    int   data_index        = 0;
    logic ready             = 0;
    int   ready_latency_cnt = 0;
    int   valid_cnt         = 0;

    function new (string name, uvm_component parent);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
        hi_tr = null;
        reset_sync = new();
    endfunction

    virtual function void write(uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) tr);

        logic [EMPTY_WIDTH-1 : 0] eop_pos[REGIONS];
        int unsigned pos_end = 0;
        logic inframe = 1'b0;

        if (reset_sync.has_been_reset()) begin
            hi_tr = null;
        end

        if (READY_LATENCY != 0) begin
            if (tr.ready == 1'b1) begin
                ready_latency_cnt = 0;
                if (|tr.valid == 0 && inframe) begin
                    valid_cnt++;
                    if (valid_cnt > READY_LATENCY)
                        `uvm_error(this.get_full_name(), "\n\tValid has not been triggered within READY_LATENCY inside of frame")
                end
            end else begin
                if (|tr.valid) begin
                    ready_latency_cnt++;
                    if (ready_latency_cnt > READY_LATENCY)
                        `uvm_error(this.get_full_name(), "\n\tReady latency is higher than allowed")
                end
            end
        end else if (|tr.valid == 0 || tr.ready == 0) begin
            return;
        end

        for (int unsigned it = 0; it < REGIONS; it++) begin
            if (tr.valid[it]) begin

                eop_pos[it] = ~tr.empty[it];
                pos_end = tr.eop[it] ? eop_pos[it] : (REGION_SIZE*BLOCK_SIZE-1);

                if (tr.sop[it]) begin
                    if (hi_tr != null) begin
                        `uvm_error(this.get_full_name(), "\n\tSOF has been set before previous frame haven't correctly ended. EOF haven't been set on end of packet")
                    end
                    inframe = 1'b1;
                    hi_tr = uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)::type_id::create("hi_tr");
                    data.delete();
                end

                if (hi_tr != null) begin
                    for (int unsigned jt = 0; jt <= pos_end; jt++) begin
                        data.push_back(tr.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH]);
                        data_index++;
                    end
                end

                if (tr.eop[it] && hi_tr != null) begin
                    if (hi_tr == null) begin
                        `uvm_error(this.get_full_name(), "\n\tEOF has been set before frame heve been started. SOF havent been set before this EOF")
                    end else begin
                        inframe = 1'b0;
                        hi_tr.data = data;
                        hi_tr.start[this.get_full_name()] = $time();
                        analysis_port.write(hi_tr);
                        hi_tr = null;
                    end
                end

            end
        end

    endfunction
endclass

class monitor_logic_vector #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH, int unsigned READY_LATENCY) extends uvm_logic_vector::monitor#(META_WIDTH);
    `uvm_component_param_utils(uvm_logic_vector_array_avst::monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY))

    typedef monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY) this_type;
    // Analysis port
    uvm_analysis_imp #(uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH), this_type) analysis_export;

    uvm_reset::sync_terminate reset_sync;
    config_item::meta_type    meta_behav;

    int   ready_latency_cnt = 0;
    int   valid_cnt         = 0;

    local uvm_logic_vector::sequence_item#(META_WIDTH) hi_tr;

    function new (string name, uvm_component parent);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
        reset_sync = new();
    endfunction

    virtual function void write(uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) tr);
        logic inframe = 1'b0;

        if (READY_LATENCY != 0) begin
            if (tr.ready == 1'b1) begin
                ready_latency_cnt = 0;
                if (|tr.valid == 0 && inframe) begin
                    valid_cnt++;
                    if (valid_cnt > READY_LATENCY)
                        `uvm_error(this.get_full_name(), "\n\tValid has not been triggered within READY_LATENCY inside of frame")
                end
            end else begin
                if (|tr.valid) begin
                    ready_latency_cnt++;
                    if (ready_latency_cnt > READY_LATENCY)
                        `uvm_error(this.get_full_name(), "\n\tReady latency is higher than allowed")
                end
            end
        end else if (|tr.valid == 0 || tr.ready == 0) begin
            return;
        end

        for (int it = 0; it < REGIONS; it++) begin
            if (tr.valid[it]) begin
                if (tr.sop[it] && meta_behav == config_item::META_SOF) begin
                    inframe = 1'b1;
                    hi_tr = uvm_logic_vector::sequence_item#(META_WIDTH)::type_id::create("hi_tr");
                    hi_tr.data = tr.meta[it];
                    hi_tr.start[this.get_full_name()] = $time();
                    analysis_port.write(hi_tr);
                end else if (tr.eop[it] && meta_behav == config_item::META_EOF) begin
                    inframe = 1'b0;
                    hi_tr = uvm_logic_vector::sequence_item#(META_WIDTH)::type_id::create("hi_tr");
                    hi_tr.data = tr.meta[it];
                    hi_tr.start[this.get_full_name()] = $time();
                    analysis_port.write(hi_tr);
                end
        end
       end

    endfunction
endclass
