//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class scoreboard_mfb #(MFB_BLOCK_SIZE, type CLASS_TYPE) extends uvm_common::comparer_base_unordered#(CLASS_TYPE, CLASS_TYPE);
    `uvm_component_param_utils(uvm_pcie_adapter::scoreboard_mfb #(MFB_BLOCK_SIZE, CLASS_TYPE))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        int unsigned model_len   = 0;
        int unsigned model_align = 0;
        int unsigned dut_len     = 0;
        int unsigned ret         = 0;

        model_len = tr_model.size();
        dut_len   = tr_dut.size();
        model_align = ((model_len % MFB_BLOCK_SIZE) != 0) ? (MFB_BLOCK_SIZE - model_len % MFB_BLOCK_SIZE) : 0;

        if (dut_len >= model_len && dut_len <= (model_len + model_align)) begin
            ret = 1;
            for (int unsigned it = 0; it < model_len; it++) begin
                if (tr_model.data[it] != tr_dut.data[it]) begin
                    ret = 0;
                end
            end
        end
        return ret;
    endfunction

endclass
