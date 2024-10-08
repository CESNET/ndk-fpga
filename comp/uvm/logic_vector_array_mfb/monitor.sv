//-- monitor.sv: Monitor for MFB environment
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class monitor_logic_vector_array #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_logic_vector_array::monitor #(ITEM_WIDTH);
    `uvm_component_param_utils(uvm_logic_vector_array_mfb::monitor_logic_vector_array #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    // Analysis port
    typedef monitor_logic_vector_array #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) this_type;
    uvm_analysis_imp #(uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH), this_type) analysis_export;

    uvm_reset::sync_terminate reset_sync;
    localparam SOF_POS_WIDTH = $clog2(REGION_SIZE);
    protected int unsigned items;
    protected uvm_logic_vector_array::sequence_item #(ITEM_WIDTH) hi_tr;
    protected logic [ITEM_WIDTH-1 : 0] data[$];

    function new (string name, uvm_component parent);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
        hi_tr = null;
        items = 0;
        reset_sync = new();
    endfunction

    virtual function void process_eof(int unsigned index, uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) tr);
        if (hi_tr != null) begin
            hi_tr.data = data;
            items++;
            hi_tr.set_transaction_id(items);
            hi_tr.start[this.get_full_name()] = $time();
            analysis_port.write(hi_tr);
            hi_tr = null;
        end else begin
            `uvm_error(this.get_full_name(), "\n\n\tTwo EOFs without a SOF between them were detected!\nThe frame's SOF is missing or an EOF has been duplicated.\n")
        end
    endfunction

    virtual function void process_sof(int unsigned index, int unsigned end_pos, uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) tr);
        int unsigned sof_pos = (SOF_POS_WIDTH != 0 ? BLOCK_SIZE*tr.sof_pos[index] : 0);

        if (hi_tr != null) begin
            `uvm_error(this.get_full_name(), "\n\n\tTwo SOFs without an EOF between them were detected!\nThe frame's EOF is missing or a SOF has been duplicated.\n")
        end
        hi_tr = uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)::type_id::create("hi_tr", this);
        data.delete();
        for (int unsigned it = sof_pos; it <= end_pos; it++) begin
            data.push_back(tr.data[index][(it+1)*ITEM_WIDTH-1 -: ITEM_WIDTH]);
        end
    endfunction


    virtual function void write(uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) tr);
        int unsigned inframe = 0;

        if (reset_sync.has_been_reset()) begin
            hi_tr = null;
        end

        if (tr.src_rdy == 1'b1 && tr.dst_rdy == 1'b1 && !reset_sync.is_reset()) begin
            for (int unsigned it = 0; it < REGIONS; it++) begin
                //$write("MFB MON FIFO %h\n", tr.data[it]);
                int unsigned sof_pos = SOF_POS_WIDTH != 0 ? BLOCK_SIZE*tr.sof_pos[it] : 0;
                // Eop is before next packet start
                if (tr.sof[it] && tr.eof[it] && tr.eof_pos[it] < sof_pos) begin
                    inframe = 1;
                    for (int unsigned jt = 0; jt <= tr.eof_pos[it]; jt++) begin
                        data.push_back(tr.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH]);
                    end
                    process_eof(it, tr);
                    process_sof(it, REGION_SIZE*BLOCK_SIZE-1, tr);
                end else begin

                    int unsigned pos_end = tr.eof[it] ? tr.eof_pos[it] : (REGION_SIZE*BLOCK_SIZE-1);

                    if (tr.sof[it]) begin
                        inframe = 1;
                        process_sof(it, pos_end, tr);
                    end else if (hi_tr != null) begin
                        inframe = 1;
                        for (int unsigned jt = 0; jt <= pos_end; jt++) begin
                            data.push_back(tr.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH]);
                        end
                    end

                    if (tr.eof[it]) begin
                        process_eof(it, tr);
                    end
                end
            end

            if (inframe == 0) begin
                `uvm_error(this.get_full_name(), "\n\tSRC RDY is set outside of frame!");
            end
        end
    endfunction
endclass

class monitor_logic_vector #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_logic_vector::monitor#(META_WIDTH);
    `uvm_component_param_utils(uvm_logic_vector_array_mfb::monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    //localparam ITEM_WIDTH = 32;

    typedef monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) this_type;
    // Analysis por
    uvm_analysis_imp #(uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH), this_type) analysis_export;
    uvm_reset::sync_terminate reset_sync;
    config_item::meta_type meta_behav;

    protected int unsigned items;
    protected uvm_logic_vector::sequence_item#(META_WIDTH) hi_tr;

    function new (string name, uvm_component parent);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
        reset_sync = new();
        items = 0;
    endfunction

    virtual function void write(uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) tr);
        if (tr.src_rdy && tr.dst_rdy) begin
            for (int i = 0; i<REGIONS; i++) begin
                if (tr.sof[i] && meta_behav == config_item::META_SOF) begin
                    hi_tr = uvm_logic_vector::sequence_item#(META_WIDTH)::type_id::create("hi_tr");
                    hi_tr.data = tr.meta[i];
                    items++;
                    hi_tr.set_transaction_id(items);
                    hi_tr.start[this.get_full_name()] = $time();
                    analysis_port.write(hi_tr);
                end else if (tr.eof[i] && meta_behav == config_item::META_EOF) begin
                    hi_tr = uvm_logic_vector::sequence_item#(META_WIDTH)::type_id::create("hi_tr");
                    hi_tr.data = tr.meta[i];
                    items++;
                    hi_tr.set_transaction_id(items);
                    hi_tr.start[this.get_full_name()] = $time();
                    analysis_port.write(hi_tr);
                end
            end
       end
    endfunction
endclass
