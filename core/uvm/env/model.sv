/*
 * file       : model.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Model create expectated output from input. 
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class packet #(WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH) extends uvm_app_core_top_agent::sequence_item#(ITEM_WIDTH, WIDTH + $clog2(CHANNELS) + $clog2(PKT_MTU+1) + 1);
    `uvm_object_param_utils(uvm_app_core::packet #(WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH));

    logic [WIDTH-1:0]             meta;
    logic [$clog2(CHANNELS)-1:0]  channel;
    //logic [$clog2(PKT_MTU+1)-1:0] packet_size;
    logic discard;

    function new(string name = "uvm_app_core::packet");
        super.new(name);
    endfunction

    function void do_copy(uvm_object rhs);
        packet #(WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH)  rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "uvm_app_core::packet::do_copy:", "Failed to cast transaction object." )
            return;
        end

        // Now copy all attributes.
        super.do_copy(rhs);
        meta        = rhs_.meta;
        channel     = rhs_.channel;
        //packet_size = rhs_.packet_size;
        discard     = rhs_.discard;
    endfunction

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret = 1;
        packet #(WIDTH, CHANNELS, PKT_MTU, ITEM_WIDTH)  rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret = super.do_compare(rhs, comparer);
        ret &= (meta        === rhs_.meta);
        ret &= (channel     === rhs_.channel);
        //ret &= (packet_size === rhs_.packet_size);
        ret &= (discard     === rhs_.discard);
        return ret;
    endfunction


    function string convert2string();
        logic [$clog2(PKT_MTU+1)-1:0] packet_size;
        string msg;

        packet_size = data.size();
        msg = super.convert2string();
        msg = {msg, $sformatf("\n\tPacket form 0x%h", {discard, channel, meta, packet_size})}; 
        msg = {msg, $sformatf("\n\tmeta 0x%h\n\tchannel %0d\n\tpacket size %0d\n\tdiscard %b", meta, channel, packet_size, discard)};
        return msg;
    endfunction
endclass


class model #(ETH_STREAMS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, ITEM_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_app_core::model#(ETH_STREAMS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, ITEM_WIDTH))

    // DEFINE class type
    typedef model#(ETH_STREAMS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, ITEM_WIDTH) this_type;
    //META TO ITEM

    //ETH
    localparam ETH_TX_LENGTH_WIDTH  = 16;
    localparam ETH_TX_CHANNEL_WIDTH = 8;
    // ETH_RX
    uvm_tlm_analysis_fifo #(uvm_app_core_top_agent::sequence_eth_item#(2**8, 16, ITEM_WIDTH)) eth_rx[ETH_STREAMS];
    // ETH_TX
    uvm_analysis_port #(uvm_app_core::packet #(0, 2**ETH_TX_CHANNEL_WIDTH, 2**ETH_TX_LENGTH_WIDTH-1, ITEM_WIDTH)) eth_tx[ETH_STREAMS];
    // DMA RX
    uvm_tlm_analysis_fifo #(uvm_app_core_top_agent::sequence_dma_item#(DMA_RX_CHANNELS, $clog2(DMA_PKT_MTU+1), DMA_HDR_META_WIDTH, ITEM_WIDTH))  dma_rx[DMA_STREAMS];
    // DMA TX
    uvm_analysis_port #(uvm_app_core::packet #(DMA_HDR_META_WIDTH, DMA_RX_CHANNELS, DMA_PKT_MTU, ITEM_WIDTH)) dma_tx[DMA_STREAMS];

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            eth_rx[it] = new({"eth_rx", $sformatf("_%0d", it)}, this);
        end

        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            dma_rx[it] = new({"dma_rx", $sformatf("_%0d", it)}, this);
        end
    endfunction

    function void build_phase(uvm_phase phase);
        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            eth_tx[it] = new({"eth_tx_", it_num}, this);
        end

        ///////////////
        // DMA BUILD ANALYSIS EXPORTS
        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            dma_tx[it] = new({"dma_tx_", it_num}, this);
        end
    endfunction

    virtual function void regmodel_set(uvm_app_core::regmodel m_regmodel_base);
    endfunction

    virtual function bit used();
        bit ret = 0;

        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            ret |= (eth_rx[it].used() != 0);
        end
        ///////////////
        // DMA BUILD ANALYSIS EXPORTS
        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            ret |= (dma_rx[it].used() != 0);
        end
        return 0;
    endfunction

    virtual function void reset();
        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            eth_rx[it].flush();
        end
        ///////////////
        // DMA BUILD ANALYSIS EXPORTS
        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            dma_rx[it].flush();
        end
    endfunction

    virtual task run_eth(uvm_phase phase, int unsigned index);
    endtask

    virtual task run_dma(uvm_phase phase, int unsigned index);
    endtask

    task run_phase(uvm_phase phase);
        for(int it = 0; it < ETH_STREAMS; it++) begin
            fork
                automatic int index = it;
                run_eth(phase, index);
            join_none;
        end

        for(int it = 0; it < DMA_STREAMS; it++) begin
            fork
                automatic int index = it;
                run_dma(phase, index);
            join_none;
        end
    endtask
endclass
