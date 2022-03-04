/*
 * file       : scoreboard_cmp.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description:  Scoreboard comparator 
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

virtual class scoreboard_channel #(type DUT_TYPE, MODEL_TYPE = DUT_TYPE) extends uvm_component;
    `uvm_component_param_utils(app_core::scoreboard_channel #(DUT_TYPE, MODEL_TYPE))

    typedef scoreboard_channel#(DUT_TYPE, MODEL_TYPE) this_type;
    //
    uvm_analysis_imp_dut#(DUT_TYPE, this_type)   analysis_imp_dut;
    uvm_analysis_imp_model#(MODEL_TYPE, this_type) analysis_imp_model;

    DUT_TYPE   data_dut[$];
    MODEL_TYPE data_model[$];

    int unsigned compared = 0;
    int unsigned errors   = 0;

    string prefix = "DMA [%0d] packet";

    function new(string name, uvm_component parent = null);
        super.new(name, parent);

        analysis_imp_model = new("analysis_imp_model", this);
        analysis_imp_dut   = new("analysis_imp_dut", this);
    endfunction

    function void prefix_set(string prefix);
        this.prefix = prefix;
    endfunction

    function int unsigned used();
        return (data_dut.size() != 0 || data_model.size() != 0);
    endfunction

    function void flush();
        data_dut.delete();
        data_model.delete();
    endfunction

    virtual function void write_dut(DUT_TYPE t);
        data_dut.push_back(t);
    endfunction

    virtual function void write_model(MODEL_TYPE t);
        data_model.push_back(t);
    endfunction

    pure virtual function bit compare(DUT_TYPE tr_dut, MODEL_TYPE tr_model);
    pure virtual function string message(DUT_TYPE tr_dut, MODEL_TYPE tr_model);

    virtual task run_phase(uvm_phase phase);
        MODEL_TYPE tr_model;
        DUT_TYPE   tr_dut;

        forever begin
            wait(data_dut.size() != 0 && data_model.size() != 0);

            tr_dut   = data_dut.pop_front();
            tr_model = data_model.pop_front();

            compared++;
            if (!this.compare(tr_dut, tr_model)) begin
                errors++;
                `uvm_error(this.get_full_name(), this.message(tr_dut, tr_model));
            end
        end
    endtask
endclass

class scoreboard_channel_mfb #(type CLASS_TYPE) extends scoreboard_channel #(CLASS_TYPE, CLASS_TYPE);
    `uvm_component_param_utils(app_core::scoreboard_channel_mfb #(CLASS_TYPE))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function bit compare(CLASS_TYPE tr_dut, CLASS_TYPE tr_model);
        return tr_model.compare(tr_dut);
    endfunction

    virtual function string message(CLASS_TYPE tr_dut, CLASS_TYPE tr_model);
        string msg;
        $swrite(msg, "\n\t%s isnt same as model predict. Erros %0d Packets %0d", prefix, errors, compared);
        $swrite(msg, "%s\n\tDUT PACKET %s\n\n",   msg, tr_dut.convert2string());
        $swrite(msg, "%s\n\tMODEL PACKET%s\n\n",  msg, tr_model.convert2string());
        return msg;
    endfunction
endclass

class scoreboard_channel_header #(HDR_WIDTH, META_WIDTH, CHANNELS, PKT_MTU) extends scoreboard_channel #(logic_vector::sequence_item#(HDR_WIDTH), packet_header #(META_WIDTH, CHANNELS, PKT_MTU));
    `uvm_component_param_utils(app_core::scoreboard_channel_header #(HDR_WIDTH, META_WIDTH, CHANNELS, PKT_MTU))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function bit compare(logic_vector::sequence_item#(HDR_WIDTH) tr_dut, packet_header #(META_WIDTH, CHANNELS, PKT_MTU) tr_model);
        bit   eq = 1;
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
        eq &= (packet_size === tr_model.packet_size);

        return eq;
    endfunction

    virtual function string message(logic_vector::sequence_item#(HDR_WIDTH) tr_dut, packet_header #(META_WIDTH, CHANNELS, PKT_MTU) tr_model);
        string error_msg; //ETH [%0d] header
        logic [META_WIDTH-1:0]meta = 'x;
        logic [$clog2(CHANNELS)-1:0] channel;
        logic [$clog2(PKT_MTU+1)] packet_size;
        logic discard;

        if (META_WIDTH == 0) begin
            {discard, channel, packet_size} = tr_dut.data;
        end else begin
            {discard, channel, meta, packet_size} = tr_dut.data; 
        end
        $swrite(error_msg, "\n\t%s isnt same as model predict [DUT model] errors %0d compared %0d", prefix, errors, compared);
        $swrite(error_msg, "%s\n\t\tdiscard [%b %b]", error_msg, discard, tr_model.discard);
        $swrite(error_msg, "%s\n\t\tchannel [%0d %0d]", error_msg, channel, tr_model.channel);
        $swrite(error_msg, "%s\n\t\tmeta    [%h %h]", error_msg, meta, tr_model.meta);
        $swrite(error_msg, "%s\n\t\tpacket_size [%0d %0d]", error_msg, packet_size, tr_model.packet_size);

        return error_msg;
    endfunction
endclass

