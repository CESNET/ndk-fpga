//-- monitor.sv: Monitor for MFB environment
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class monitor_axi_lva #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_logic_vector_array::monitor #(ITEM_WIDTH);

    `uvm_component_param_utils(monitor_axi_lva #(ITEMS, ITEM_WIDTH))

    // Analysis export
    uvm_analysis_imp #(
        uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, 0),
        monitor_axi_lva #(ITEMS, ITEM_WIDTH)
    ) analysis_export;

    // Internal state
    //uvm_logic_vector_array::sequence_item #(ITEM_WIDTH) hi_tr;
    protected logic [ITEM_WIDTH-1 : 0] data[$];
    protected int unsigned items;
    protected time start_time;

    // Reset sync
    uvm_reset::sync_terminate reset_sync;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        analysis_port = new("analysis_port", this);
        analysis_export = new("analysis_export", this);
        items = 0;
        data  = {};
        reset_sync = new();
    endfunction

    virtual function void write(uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, 0) tr);

        if (reset_sync.has_been_reset()) begin
            data = {};
        end

        if (reset_sync.is_reset()) begin
            return;
        end

        if (tr.tvalid && tr.tready) begin
            if(data.size() == 0) begin
                start_time = $time;
            end

            for (int unsigned it = 0; it < ITEMS; it++) begin
                logic [ITEM_WIDTH-1 : 0] item_data;
                item_data = tr.tdata[(it+1)*ITEM_WIDTH-1 -: ITEM_WIDTH];
                data.push_back(item_data);
            end

            if (tr.tlast) begin
                uvm_logic_vector_array::sequence_item #(ITEM_WIDTH) hi_tr;

                hi_tr = uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)::type_id::create("hi_tr", this);
                hi_tr.data = data;
                hi_tr.set_transaction_id(items);
                hi_tr.start[this.get_full_name()] = start_time;
                analysis_port.write(hi_tr);

                items++;
                data.delete();
            end
        end
    endfunction
endclass

