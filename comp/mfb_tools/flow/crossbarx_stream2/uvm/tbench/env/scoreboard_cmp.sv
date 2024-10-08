// scoreboard_cmp.sv: CMP for verification
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class cxs2_comparer #(type CLASS_TYPE) extends uvm_common::comparer_ordered#(CLASS_TYPE);
    `uvm_component_param_utils(uvm_mfb_crossbarx_stream2::cxs2_comparer #(CLASS_TYPE))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        int unsigned ret = 1;
        if (tr_model.data.size() != tr_dut.data.size()) return 0;
        for (int unsigned it = 0; it < tr_model.size(); it++) begin
            if (!$isunknown(tr_model.data[it]) && tr_model.data[it] !== tr_dut.data[it]) begin
                return 0;
            end
        end

        `uvm_info(this.get_full_name(), $sformatf("\n======= COMPARE: Transaction %0d =======\nMODEL ITEM : %s\nDUT ITEM : %s\n", compared, model_item2string(tr_model), dut_item2string(tr_dut)), UVM_MEDIUM);
        return ret;
    endfunction

endclass
