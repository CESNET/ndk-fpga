//-- tr_planner.sv: Transaction planner
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class tr_planner #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_pcie_adapter::tr_planner #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    uvm_analysis_imp#(uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH), tr_planner #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)) analysis_imp;
    uvm_logic_vector::sequence_item #(META_WIDTH) tr_array[$];
    uvm_logic_vector::sequence_item#(META_WIDTH) meta;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        analysis_imp = new("analysis_imp", this);
    endfunction

    virtual function void write(uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) req);

        for (int unsigned it = 0; it < REGIONS; it++) begin
            if (req.valid[it]) begin
                if (req.sop[it]) begin
                    meta = uvm_logic_vector::sequence_item#(META_WIDTH)::type_id::create("meta");
                    meta.data = req.meta[it];
                end
                if (req.eop[it]) begin
                    tr_array.push_back(meta);
                end
            end
        end
    endfunction
endclass
