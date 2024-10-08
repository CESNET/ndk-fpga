// scoreboard_cmp.sv: CMP for verification
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

//Note: use comparer_ordered in case of one channel setting
class comparer_superpacket #(type CLASS_TYPE) extends uvm_common::comparer_taged#(CLASS_TYPE); // comparer_ordered#(CLASS_TYPE);
    `uvm_component_param_utils(uvm_framepacker::comparer_superpacket #(CLASS_TYPE))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        int unsigned ret = 1;
        if (tr_model.data.size() < tr_dut.data.size()) return 0;
        for (int unsigned it = 0; it < tr_model.size(); it++) begin
            if (!$isunknown(tr_model.data[it]) && tr_model.data[it] !== tr_dut.data[it]) begin
                return 0;
            end
        end
        return ret;
    endfunction

endclass

class comparer_meta #(RX_CHANNELS, PKT_MTU, META_WIDTH) extends uvm_common::comparer_unordered#(uvm_logic_vector::sequence_item #($clog2(RX_CHANNELS) + $clog2(PKT_MTU+1) + META_WIDTH + 1));
    `uvm_component_param_utils(uvm_framepacker::comparer_meta #(RX_CHANNELS, PKT_MTU, META_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        int unsigned ret = 1;

        logic [$clog2(RX_CHANNELS)-1:0] model_channel;
        logic [$clog2(PKT_MTU+1)-1:0]   model_length;
        logic [META_WIDTH-1:0]          model_meta;
        logic                           model_discard;

        logic [$clog2(RX_CHANNELS)-1:0] dut_channel;
        logic [$clog2(PKT_MTU+1)-1:0]   dut_length;
        logic [META_WIDTH-1:0]          dut_meta;
        logic                           dut_discard;

        {model_length, model_meta, model_discard, model_channel} = tr_model.data;
        {dut_length, dut_meta, dut_discard, dut_channel} = tr_dut.data;

        ret &= $isunknown(model_length)  || (model_length  === dut_length);
        ret &= $isunknown(model_channel) || (model_channel === dut_channel);
        ret &= $isunknown(model_meta)    || (model_meta    === dut_meta);
        ret &= $isunknown(model_discard) || (model_discard === dut_discard);

        return ret;
    endfunction

    virtual function string model_item2string(MODEL_ITEM tr);
        logic [$clog2(RX_CHANNELS)-1:0] channel;
        logic [$clog2(PKT_MTU+1)-1:0]   length;
        logic [META_WIDTH-1:0]          meta;
        logic                           discard;

        return tr.convert2string();
    endfunction

    virtual function string dut_item2string(DUT_ITEM   tr);
        return tr.convert2string();
    endfunction

endclass
