/*
 * file       : scoreboard_cmp.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description:  Scoreboard comparator 
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class scoreboard_cmp_header #(type MODEL_ITEM, type DUT_ITEM, int unsigned META_WIDTH, int unsigned CHANNELS, int unsigned PKT_MTU);

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        int unsigned eq = 1;
        logic [META_WIDTH-1:0]meta = 'x;
        logic [$clog2(CHANNELS)-1:0] channel;
        logic [$clog2(PKT_MTU+1)] packet_size;
        logic discard;

        if (META_WIDTH == 0) begin
            {discard, channel, packet_size} = tr_dut.data;
        end else begin
            {discard, channel, meta, packet_size} = tr_dut.data;
        end

        eq &= (discard === tr_model.discard);
        eq &= (channel === tr_model.channel);
        if (META_WIDTH != 0) begin
            eq &= (meta    === tr_model.meta);
        end
        eq &= (packet_size === tr_model.data.size());

        return eq;
    endfunction

    virtual function string model_item2string(MODEL_ITEM tr);
        string msg; //ETH [%0d] header
        msg = tr.time2string();
        msg = {msg, $sformatf("\n\t\tdiscard %b",  tr.discard)};
        msg = {msg, $sformatf("\n\t\tchannel %0d", tr.channel)};
        msg = {msg, $sformatf("\n\t\tmeta    0x%h",  tr.meta)};
        msg = {msg, $sformatf("\n\t\tpacket_size %0d", tr.data.size())};

        return msg;
    endfunction

    virtual function string dut_item2string(DUT_ITEM tr);
        string error_msg; //ETH [%0d] header
        logic [META_WIDTH-1:0]meta = 'x;
        logic [$clog2(CHANNELS)-1:0] channel;
        logic [$clog2(PKT_MTU+1)] packet_size;
        logic discard;

        if (META_WIDTH == 0) begin
            {discard, channel, packet_size} = tr.data;
        end else begin
            {discard, channel, meta, packet_size} = tr.data;
        end

        error_msg = tr.time2string();
        error_msg = {error_msg, $sformatf("\n\t\tdiscard %b", discard)};
        error_msg = {error_msg, $sformatf("\n\t\tchannel %0d", channel)};
        error_msg = {error_msg, $sformatf("\n\t\tmeta    0x%h",  meta)};
        error_msg = {error_msg, $sformatf("\n\t\tpacket_size %0d", packet_size)};

        return error_msg;
    endfunction
endclass

class scoreboard_channel_mfb_unordered #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH) extends uvm_common::comparer_base_unordered#(packet #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH), uvm_logic_vector_array::sequence_item#(ITEM_WIDTH));
    `uvm_component_param_utils(uvm_app_core::scoreboard_channel_mfb_unordered #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        return (tr_dut.data ==? tr_model.data);
    endfunction

    virtual function string model_item2string(MODEL_ITEM tr);
        return tr.convert2string();
    endfunction

    virtual function string dut_item2string(DUT_ITEM tr);
        return tr.convert2string();
    endfunction
endclass

class scoreboard_channel_mfb_ordered #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH) extends uvm_common::comparer_base_ordered#(packet #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH), uvm_logic_vector_array::sequence_item#(ITEM_WIDTH));
    `uvm_component_param_utils(uvm_app_core::scoreboard_channel_mfb_ordered #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        return (tr_dut.data ==? tr_model.data);
    endfunction

    virtual function string model_item2string(MODEL_ITEM tr);
        return tr.convert2string();
    endfunction

    virtual function string dut_item2string(DUT_ITEM tr);
        return tr.convert2string();
    endfunction
endclass

class scoreboard_channel_mfb_tagged #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH) extends uvm_common::comparer_base_tagged#(packet #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH), uvm_logic_vector_array::sequence_item#(ITEM_WIDTH));
    `uvm_component_param_utils(uvm_app_core::scoreboard_channel_mfb_tagged #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        return (tr_dut.data ==? tr_model.data);
    endfunction

    virtual function string model_item2string(MODEL_ITEM tr);
        return tr.convert2string();
    endfunction

    virtual function string dut_item2string(DUT_ITEM tr);
        return tr.convert2string();
    endfunction
endclass


class scoreboard_channel_header_unordered #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH) extends uvm_common::comparer_base_unordered #(packet #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH), uvm_logic_vector::sequence_item#(META_WIDTH + $clog2(CHANNELS) + $clog2(PKT_MTU+1) + 1));
    `uvm_component_param_utils(uvm_app_core::scoreboard_channel_header_unordered #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH))

    protected scoreboard_cmp_header #(MODEL_ITEM, DUT_ITEM, META_WIDTH, CHANNELS, PKT_MTU) cmp;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        cmp = new();
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        return cmp.compare(tr_model, tr_dut);
    endfunction

    virtual function string model_item2string(MODEL_ITEM tr);
        return cmp.model_item2string(tr);
    endfunction

    virtual function string dut_item2string(DUT_ITEM tr);
        return cmp.dut_item2string(tr);
    endfunction
endclass

class scoreboard_channel_header_ordered #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH) extends uvm_common::comparer_base_ordered #(packet #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH), uvm_logic_vector::sequence_item#(META_WIDTH + $clog2(CHANNELS) + $clog2(PKT_MTU+1) + 1));
    `uvm_component_param_utils(uvm_app_core::scoreboard_channel_header_ordered #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH))

    protected scoreboard_cmp_header #(MODEL_ITEM, DUT_ITEM, META_WIDTH, CHANNELS, PKT_MTU) cmp;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        cmp = new();
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        return cmp.compare(tr_model, tr_dut);
    endfunction

    virtual function string model_item2string(MODEL_ITEM tr);
        return cmp.model_item2string(tr);
    endfunction

    virtual function string dut_item2string(DUT_ITEM tr);
        return cmp.dut_item2string(tr);
    endfunction
endclass


class scoreboard_channel_header_tagged #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH) extends uvm_common::comparer_base_tagged #(packet #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH), uvm_logic_vector::sequence_item#(META_WIDTH + $clog2(CHANNELS) + $clog2(PKT_MTU+1) + 1));
    `uvm_component_param_utils(uvm_app_core::scoreboard_channel_header_tagged #(META_WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH))

    protected scoreboard_cmp_header #(MODEL_ITEM, DUT_ITEM, META_WIDTH, CHANNELS, PKT_MTU) cmp;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        cmp = new();
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        return cmp.compare(tr_model, tr_dut);
    endfunction

    virtual function string model_item2string(MODEL_ITEM tr);
        return cmp.model_item2string(tr);
    endfunction

    virtual function string dut_item2string(DUT_ITEM tr);
        return cmp.dut_item2string(tr);
    endfunction
endclass

