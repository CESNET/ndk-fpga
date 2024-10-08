//-- scoreboard_cmp.sv: scoreboard 
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class comparer_tx_hdr #(int unsigned ITEM_WIDTH) extends uvm_common::comparer_base_ordered#(uvm_logic_vector::sequence_item#(ITEM_WIDTH), uvm_logic_vector::sequence_item#(ITEM_WIDTH));
    `uvm_component_param_utils(uvm_network_mod_env::comparer_tx_hdr#(ITEM_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        int unsigned ret = 1;
        logic [16-1:0] dut_length;
        logic [8-1:0]  dut_port;
        logic [1-1:0]  dut_error;
        logic [1-1:0]  dut_error_frame;
        logic [1-1:0]  dut_error_min_tu;
        logic [1-1:0]  dut_error_max_tu;
        logic [1-1:0]  dut_error_crc;
        logic [1-1:0]  dut_error_mac;
        logic [1-1:0]  dut_broadcast;
        logic [1-1:0]  dut_multicast;
        logic [1-1:0]  dut_mac_hit_vld;
        logic [4-1:0]  dut_mac_hit;
        logic [1-1:0]  dut_timestamp_vld;
        logic [64-1:0] dut_timestamp;

        logic [16-1:0] model_length;
        logic [8-1:0]  model_port;
        logic [1-1:0]  model_error;
        logic [1-1:0]  model_error_frame;
        logic [1-1:0]  model_error_min_tu;
        logic [1-1:0]  model_error_max_tu;
        logic [1-1:0]  model_error_crc;
        logic [1-1:0]  model_error_mac;
        logic [1-1:0]  model_broadcast;
        logic [1-1:0]  model_multicast;
        logic [1-1:0]  model_mac_hit_vld;
        logic [4-1:0]  model_mac_hit;
        logic [1-1:0]  model_timestamp_vld;
        logic [64-1:0] model_timestamp;

        {dut_timestamp, dut_timestamp_vld, dut_mac_hit, dut_mac_hit_vld, dut_multicast, dut_broadcast, dut_error_mac, dut_error_crc, dut_error_max_tu, dut_error_min_tu, dut_error_frame, dut_error, dut_port, dut_length} = tr_dut.data;
        {model_timestamp, model_timestamp_vld, model_mac_hit, model_mac_hit_vld, model_multicast, model_broadcast, model_error_mac, model_error_crc, model_error_max_tu, model_error_min_tu, model_error_frame, model_error, model_port, model_length} = tr_model.data;

        ret &= dut_length === model_length            ; 
        ret &= dut_port === model_port                ;
        ret &= dut_error === model_error              ;
        ret &= dut_error_frame === model_error_frame  ;
        ret &= dut_error_min_tu === model_error_min_tu;
        ret &= dut_error_max_tu === model_error_max_tu;
        ret &= dut_error_crc === model_error_crc      ;
        ret &= dut_error_mac === model_error_mac      ;
        ret &= dut_broadcast === model_broadcast      ;
        ret &= dut_multicast === model_multicast      ;
        ret &= dut_mac_hit_vld === model_mac_hit_vld ;
        ret &= (model_mac_hit_vld === 1'b0 || dut_mac_hit === model_mac_hit);
        ret &= dut_timestamp_vld === model_timestamp_vld;
        ret &= (model_timestamp_vld === 1'b0 || dut_timestamp === model_timestamp); 

        return ret;
    endfunction

    virtual function string model_item2string(MODEL_ITEM tr);
        string msg;
        logic [16-1:0] model_length;
        logic [8-1:0]  model_port;
        logic [1-1:0]  model_error;
        logic [1-1:0]  model_error_frame;
        logic [1-1:0]  model_error_min_tu;
        logic [1-1:0]  model_error_max_tu;
        logic [1-1:0]  model_error_crc;
        logic [1-1:0]  model_error_mac;
        logic [1-1:0]  model_broadcast;
        logic [1-1:0]  model_multicast;
        logic [1-1:0]  model_mac_hit_vld;
        logic [4-1:0]  model_mac_hit;
        logic [1-1:0]  model_timestamp_vld;
        logic [64-1:0] model_timestamp;

        {model_timestamp, model_timestamp_vld, model_mac_hit, model_mac_hit_vld, model_multicast, model_broadcast, model_error_mac, model_error_crc, model_error_max_tu, model_error_min_tu, model_error_frame, model_error, model_port, model_length} = tr.data;

        msg = tr.time2string();
        msg = {msg, $sformatf("\n\tlength        [%0d]" , model_length)}; 
        msg = {msg, $sformatf("\n\tport          [%0d]" , model_port)}; 
        msg = {msg, $sformatf("\n\terror         [0x%h]", model_error)}; 
        msg = {msg, $sformatf("\n\terror frame   [0x%h]", model_error_frame)}; 
        msg = {msg, $sformatf("\n\terror min MTU [0x%h]", model_error_min_tu)}; 
        msg = {msg, $sformatf("\n\terror max MTU [0x%h]", model_error_max_tu)}; 
        msg = {msg, $sformatf("\n\terror CRC     [0x%h]", model_error_crc)}; 
        msg = {msg, $sformatf("\n\terror MAC     [0x%h]", model_error_mac)}; 
        msg = {msg, $sformatf("\n\tbroadcast     [0x%h]", model_broadcast)}; 
        msg = {msg, $sformatf("\n\tmulticast     [0x%h]", model_multicast)}; 
        msg = {msg, $sformatf("\n\tMAC HIT VLD   [0x%h]", model_mac_hit_vld)}; 
        msg = {msg, $sformatf("\n\t\tMAC HIT     [0x%h]", model_mac_hit)}; 
        msg = {msg, $sformatf("\n\ttimestamp VLD [0x%h]", model_timestamp_vld)}; 
        msg = {msg, $sformatf("\n\t\ttimestamp   [0x%h]", model_timestamp)}; 
        return msg;
    endfunction

    virtual function string dut_item2string(DUT_ITEM tr);
        string msg;
        logic [16-1:0] dut_length;
        logic [8-1:0]  dut_port;
        logic [1-1:0]  dut_error;
        logic [1-1:0]  dut_error_frame;
        logic [1-1:0]  dut_error_min_tu;
        logic [1-1:0]  dut_error_max_tu;
        logic [1-1:0]  dut_error_crc;
        logic [1-1:0]  dut_error_mac;
        logic [1-1:0]  dut_broadcast;
        logic [1-1:0]  dut_multicast;
        logic [1-1:0]  dut_mac_hit_vld;
        logic [4-1:0]  dut_mac_hit;
        logic [1-1:0]  dut_timestamp_vld;
        logic [64-1:0] dut_timestamp;

        {dut_timestamp, dut_timestamp_vld, dut_mac_hit, dut_mac_hit_vld, dut_multicast, dut_broadcast, dut_error_mac, dut_error_crc, dut_error_max_tu, dut_error_min_tu, dut_error_frame, dut_error, dut_port, dut_length} = tr.data;

        msg = tr.time2string();
        msg = {msg, $sformatf("\n\tlength        [%0d]" , dut_length)}; 
        msg = {msg, $sformatf("\n\tport          [%0d]" , dut_port)}; 
        msg = {msg, $sformatf("\n\terror         [0x%h]", dut_error)}; 
        msg = {msg, $sformatf("\n\terror frame   [0x%h]", dut_error_frame)}; 
        msg = {msg, $sformatf("\n\terror min MTU [0x%h]", dut_error_min_tu)}; 
        msg = {msg, $sformatf("\n\terror max MTU [0x%h]", dut_error_max_tu)}; 
        msg = {msg, $sformatf("\n\terror CRC     [0x%h]", dut_error_crc)}; 
        msg = {msg, $sformatf("\n\terror MAC     [0x%h]", dut_error_mac)}; 
        msg = {msg, $sformatf("\n\tbroadcast     [0x%h]", dut_broadcast)}; 
        msg = {msg, $sformatf("\n\tmulticast     [0x%h]", dut_multicast)}; 
        msg = {msg, $sformatf("\n\tMAC HIT VLD   [0x%h]", dut_mac_hit_vld)}; 
        msg = {msg, $sformatf("\n\t\tMAC HIT     [0x%h]", dut_mac_hit)}; 
        msg = {msg, $sformatf("\n\ttimestamp VLD [0x%h]", dut_timestamp_vld)}; 
        msg = {msg, $sformatf("\n\t\ttimestamp   [0x%h]", dut_timestamp)}; 
        return msg;
    endfunction
endclass

