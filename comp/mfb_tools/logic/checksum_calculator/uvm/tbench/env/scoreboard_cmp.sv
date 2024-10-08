// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class chsum_calc_cmp #(MVB_DATA_WIDTH, MFB_META_WIDTH) extends uvm_common::comparer_base_ordered#(uvm_checksum_calculator::chsum_calc_item#(MVB_DATA_WIDTH, MFB_META_WIDTH), uvm_logic_vector::sequence_item#(MVB_DATA_WIDTH+1+MFB_META_WIDTH));
    `uvm_component_param_utils(uvm_checksum_calculator::chsum_calc_cmp #(MVB_DATA_WIDTH, MFB_META_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        logic [MVB_DATA_WIDTH-1 : 0]  data_dut;
        logic                         bypass_dut;
        logic [MFB_META_WIDTH-1 : 0]  meta_dut;
        int unsigned  ret = 1;


        {meta_dut, bypass_dut, data_dut} = tr_dut.data;

        if (tr_model.bypass) begin
            ret &= (bypass_dut      === 1);
            ret &= meta_dut         === tr_model.meta;
        end else begin
            //|= is different that  &=. Be carefull when use what.
            ret &= data_dut    === tr_model.data;
            ret &= (bypass_dut === 0);
            ret &= meta_dut    === tr_model.meta;
        end

        return ret;
    endfunction


    virtual function string dut_item2string(DUT_ITEM tr);
        logic [MVB_DATA_WIDTH-1 : 0]  data;
        logic                         bypass;
        logic [MFB_META_WIDTH-1 : 0]  meta;
        string msg;

        {meta, bypass, data} = tr.data;
        msg = tr.time2string();
        msg = {msg, $sformatf("\n\tbypass %b",  bypass)};
        msg = {msg, $sformatf("\n\tmeta   %h",  meta)};
        msg = {msg, $sformatf("\n\tdata   %h",  data)};
        return msg;
    endfunction

    virtual function string model_item2string(MODEL_ITEM tr);
        return tr.convert2string();
    endfunction

endclass

