/*
 * file       : model.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Model create expectated output from input. 
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class packet_header #(WIDTH, CHANNELS, PKT_MTU);
    logic [WIDTH-1:0]             meta;
    logic [$clog2(CHANNELS)-1:0]  channel;
    logic [$clog2(PKT_MTU+1)-1:0] packet_size;
    logic discard;

    function string convert2string();
        string msg;

        $swrite(msg, "\n\tmeta %h\n\tchannel %0d\n\tpacket size %0d\n\tdiscard %b", meta, channel, packet_size, discard);
        return msg;
    endfunction
endclass


class model #(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, MVB_ITEMS, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_component;
    `uvm_component_param_utils(app_core::model#(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, MVB_ITEMS, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    //RESET
    typedef model#(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, MVB_ITEMS, MI_DATA_WIDTH, MI_ADDR_WIDTH) this_type;
    uvm_analysis_imp_reset#(reset::sequence_item, this_type) analysis_imp_reset;

    //ETH
    localparam ETH_TX_LENGTH_WIDTH  = 16;
    localparam ETH_TX_CHANNEL_WIDTH = 8;
    uvm_tlm_analysis_fifo #(mvb::sequence_item#(MVB_ITEMS, ETH_RX_HDR_WIDTH)) eth_mvb_rx[ETH_STREAMS];
    uvm_tlm_analysis_fifo #(byte_array::sequence_item)                        eth_mfb_rx[ETH_STREAMS];
    uvm_analysis_port     #(packet_header #(0, 2**ETH_TX_CHANNEL_WIDTH, 2**ETH_TX_LENGTH_WIDTH-1))    eth_mvb_tx[ETH_STREAMS];
    uvm_analysis_port     #(byte_array::sequence_item)                        eth_mfb_tx[ETH_STREAMS];
    //DMA
    localparam DMA_RX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_TX_CHANNELS);
    uvm_tlm_analysis_fifo #(mvb::sequence_item#(MVB_ITEMS, DMA_RX_MVB_WIDTH)) dma_mvb_rx[DMA_STREAMS];
    uvm_tlm_analysis_fifo #(byte_array::sequence_item)                        dma_mfb_rx[DMA_STREAMS];
    uvm_analysis_port     #(packet_header #(DMA_HDR_META_WIDTH, DMA_RX_CHANNELS, DMA_PKT_MTU)) dma_mvb_tx[DMA_STREAMS];
    uvm_analysis_port     #(byte_array::sequence_item)                        dma_mfb_tx[DMA_STREAMS];

    //LOCAL VARIABLES
    channel_router::model#(ETH_CHANNELS, DMA_RX_CHANNELS, 2, 1) eth_to_dma[ETH_STREAMS];
    //local int unsigned eth_to_dma_index[ETH_STREAMS] = '{ETH_STREAMS{0}};
    local logic [DMA_RX_MVB_WIDTH-1:0] dma_header[ETH_STREAMS][$];
    //local int unsigned dma_to_eth_index[DMA_STREAMS] = '{DMA_STREAMS{0}};

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        analysis_imp_reset = new("analysis_imp_reset", this);

        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            eth_mvb_rx[it] = new({"eth_mvb_rx_", it_num}, this);
            eth_mfb_rx[it] = new({"eth_mfb_rx_", it_num}, this);
            eth_mvb_tx[it] = new({"eth_mvb_tx_", it_num}, this);
            eth_mfb_tx[it] = new({"eth_mfb_tx_", it_num}, this);

            eth_to_dma[it] = channel_router::model#(ETH_CHANNELS, DMA_RX_CHANNELS, 2, 1)::type_id::create({"eth_to_dma_index_", it_num}, this);
        end

        ///////////////
        // DMA BUILD ANALYSIS EXPORTS
        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            dma_mvb_rx[it] = new({"dma_mvb_rx_", it_num}, this);
            dma_mfb_rx[it] = new({"dma_mfb_rx_", it_num}, this);
            dma_mvb_tx[it] = new({"dma_mvb_tx_", it_num}, this);
            dma_mfb_tx[it] = new({"dma_mfb_tx_", it_num}, this);
        end
    endfunction

    function void regmodel_set(app_core::regmodel #(ETH_STREAMS, ETH_CHANNELS, DMA_RX_CHANNELS) m_regmodel);
        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            this.eth_to_dma[it].regmodel_set(m_regmodel.stream[it]);
        end
    endfunction

    function bit used();
        bit used = 0;

        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            used |= (dma_header[it].size() != 0);
        end
        return used;
    endfunction

    function void write_reset(reset::sequence_item tr);
        if (tr.reset == 1'b1) begin
            for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
                eth_to_dma[it].reset();
            end

            for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
                dma_header[it].delete();
                //dma_to_eth_index[it] = 0;
            end
        end
    endfunction

    task run_eth_mvb(int unsigned index);
        logic [16-1:0] length;
        logic [8-1:0]  port;
        logic [6-1:0]  error;
        logic [1-1:0]  multicast;
        logic [1-1:0]  hitmac_vld;
        logic [4-1:0]  hitmac;
        logic [1-1:0]  timestamp_vld;
        logic [64-1:0] timestamp;
        mvb::sequence_item#(MVB_ITEMS, ETH_RX_HDR_WIDTH) item;
        logic [ETH_RX_HDR_WIDTH-1:0] header;
        byte_array::sequence_item packet;
        packet_header #(DMA_HDR_META_WIDTH, DMA_RX_CHANNELS, DMA_PKT_MTU) dma_hdr;

        forever begin
            eth_mvb_rx[index].get(item);
            if (item.SRC_RDY === 1'b1 && item.DST_RDY === 1'b1) begin
                for(int unsigned it = 0; it < MVB_ITEMS; it++) begin
                    if (item.VLD[it] == 1'b1) begin
			            {timestamp, timestamp_vld, hitmac, hitmac_vld, multicast, error, port, length} = item.DATA[it];

            			dma_hdr = new();
            			dma_hdr.meta = '0;
            			dma_hdr.channel     = eth_to_dma[index].port_get(port%ETH_CHANNELS);
            			dma_hdr.packet_size = length;
            			dma_hdr.discard     = 0;

			            dma_mvb_tx[index].write(dma_hdr);
                    end
                end
            end
        end
    endtask

    task run_eth(int unsigned index);
        logic [ETH_RX_HDR_WIDTH-1:0] header;
        byte_array::sequence_item packet;
        packet_header #(DMA_HDR_META_WIDTH, DMA_RX_CHANNELS, DMA_PKT_MTU) dma_hdr;

        forever begin
            eth_mfb_rx[index].get(packet);
            dma_mfb_tx[index].write(packet);
        end
    endtask

    task run_dma_mvb(int unsigned index);
        mvb::sequence_item#(MVB_ITEMS, DMA_RX_MVB_WIDTH) item;

        forever begin
            dma_mvb_rx[index].get(item);
            if (item.SRC_RDY === 1'b1 && item.DST_RDY === 1'b1) begin
                for(int unsigned it = 0; it < MVB_ITEMS; it++) begin
                    if (item.VLD[it] == 1'b1) begin
                        dma_header[index].push_back(item.DATA[it]);
                    end
                end
            end
        end
    endtask

    task run_dma(int unsigned index);
        int unsigned eth_stream_index;
        logic [$clog2(DMA_PKT_MTU+1)-1:0] length;
        logic [DMA_HDR_META_WIDTH-1:0]    meta;
        logic [$clog2(DMA_TX_CHANNELS)-1:0] channel;

        byte_array::sequence_item packet;
        packet_header #(0, 2**ETH_TX_CHANNEL_WIDTH, 2**ETH_TX_LENGTH_WIDTH-1) eth_hdr;
        forever begin
            dma_mfb_rx[index].get(packet);
            wait(dma_header[index].size() != 0); //wait for metainformation
            {channel, meta, length} = dma_header[index].pop_front();

            //create DMA header
            eth_hdr = new();
            eth_hdr.packet_size = length;
            eth_hdr.channel = index * ETH_CHANNELS + channel[$clog2(DMA_TX_CHANNELS)-1:$clog2(DMA_TX_CHANNELS)-$clog2(ETH_CHANNELS)]; //dma_to_eth_index[index] + index * ETH_CHANNELS);
            eth_hdr.discard = 1'b0;

            eth_mvb_tx[index].write(eth_hdr);
            eth_mfb_tx[index].write(packet);

            //dma_to_eth_index[index] = (dma_to_eth_index[index] + 1) % (ETH_CHANNELS/ETH_STREAMS);
        end
    endtask

    task run_phase(uvm_phase phase);
        for(int it = 0; it < ETH_STREAMS; it++) begin
            fork
                automatic int index = it;
                run_eth(index);
                run_eth_mvb(index);
            join_none;
        end

        for(int it = 0; it < DMA_STREAMS; it++) begin
            fork
                automatic int index = it;
                run_dma(index);
                run_dma_mvb(index);
            join_none;
        end
    endtask
endclass
