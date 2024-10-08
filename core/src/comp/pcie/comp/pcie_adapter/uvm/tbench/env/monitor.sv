//-- monitor.sv: Unit for transaction catching
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

class monitor #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) extends uvm_monitor;
    `uvm_component_param_utils(uvm_pcie_adapter::monitor #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    // Analysis port
    typedef monitor #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) this_type;
    uvm_analysis_imp #(uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH), this_type) analysis_export;
    uvm_analysis_port #(uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)) analysis_port;

    uvm_reset::sync_terminate reset_sync;
    local uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) hi_tr;

    function new (string name, uvm_component parent);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
        analysis_port   = new("analysis_port", this);
        hi_tr = null;
        reset_sync = new();
    endfunction

    virtual function void write(uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) tr);
        if (reset_sync.has_been_reset()) begin
            hi_tr = null;
        end

        hi_tr = uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("hi_tr");
        $cast(hi_tr, tr.clone());
        analysis_port.write(hi_tr);

    endfunction
endclass

