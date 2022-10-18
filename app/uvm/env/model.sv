/*
 * file       : model_minimal.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Model create expectated output from input. 
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class model #(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_app_core::model #(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_component_param_utils(uvm_app_core_minimal::model#(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH))


    // ETH_RX
    uvm_tlm_analysis_fifo #(uvm_common::model_item#(uvm_logic_vector::sequence_item#(ETH_RX_HDR_WIDTH)))                    in_eth_mvb[ETH_STREAMS];
    uvm_tlm_analysis_fifo #(uvm_common::model_item#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)))                    in_eth_mfb[ETH_STREAMS];
    // ETH_TX
    uvm_analysis_port #(uvm_common::model_item#(uvm_app_core::packet_header #(0, 2**ETH_TX_CHANNEL_WIDTH, 2**ETH_TX_LENGTH_WIDTH-1))) out_eth_mvb[ETH_STREAMS];
    uvm_analysis_port #(uvm_common::model_item#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)))                    out_eth_mfb[ETH_STREAMS];
    // DMA RX
    uvm_tlm_analysis_fifo #(uvm_common::model_item#(uvm_logic_vector::sequence_item#(DMA_RX_MVB_WIDTH)))                in_dma_mvb[DMA_STREAMS];
    uvm_tlm_analysis_fifo #(uvm_common::model_item#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)))                in_dma_mfb[DMA_STREAMS];
    // DMA TX
    uvm_analysis_port #(uvm_common::model_item#(uvm_app_core::packet_header #(DMA_HDR_META_WIDTH, DMA_RX_CHANNELS, DMA_PKT_MTU))) out_dma_mvb[DMA_STREAMS];
    uvm_analysis_port #(uvm_common::model_item#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)))                out_dma_mfb[DMA_STREAMS];


    //LOCAL VARIABLES
    protected uvm_channel_router::model#(ETH_CHANNELS, DMA_RX_CHANNELS, 2, 1) eth_to_dma[ETH_STREAMS];
    protected uvm_common::model_item#(uvm_logic_vector::sequence_item#(DMA_RX_MVB_WIDTH)) dma_hdr_fifo[DMA_STREAMS][$];

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);
            eth_to_dma[it] = uvm_channel_router::model#(ETH_CHANNELS, DMA_RX_CHANNELS, 2, 1)::type_id::create({"eth_to_dma_index_", it_num}, this);
        end

        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            in_eth_mvb[it]  = new({"in_eth_mvb_rx_", it_num}, this);
            in_eth_mfb[it]  = new({"in_eth_mfb_rx_", it_num}, this);
            out_eth_mvb[it] = new({"out_eth_mvb_tx_", it_num}, this);
            out_eth_mfb[it] = new({"out_eth_mfb_tx_", it_num}, this);
        end

        ///////////////
        // DMA BUILD ANALYSIS EXPORTS
        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            in_dma_mvb[it]  = new({"in_dma_mvb_rx_", it_num}, this);
            in_dma_mfb[it]  = new({"in_dma_mfb_rx_", it_num}, this);
            out_dma_mvb[it] = new({"out_dma_mvb_tx_", it_num}, this);
            out_dma_mfb[it] = new({"out_dma_mfb_tx_", it_num}, this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
         for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            eth_mvb_rx[it].connect(in_eth_mvb[it].analysis_export);
            eth_mfb_rx[it].connect(in_eth_mfb[it].analysis_export);
            out_eth_mvb[it].connect(eth_mvb_tx[it]);
            out_eth_mfb[it].connect(eth_mfb_tx[it]);
        end

        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            dma_mvb_rx[it].connect(in_dma_mvb[it].analysis_export);
            dma_mfb_rx[it].connect(in_dma_mfb[it].analysis_export);
            out_dma_mvb[it].connect(dma_mvb_tx[it]);
            out_dma_mfb[it].connect(dma_mfb_tx[it]);
        end
   endfunction


    virtual function void regmodel_set(uvm_app_core::regmodel #(ETH_STREAMS, ETH_CHANNELS, DMA_RX_CHANNELS) m_regmodel_base);
        uvm_app_core_minimal::regmodel #(ETH_STREAMS, ETH_CHANNELS, DMA_RX_CHANNELS) m_regmodel;

        if ($cast(m_regmodel, m_regmodel_base) != 1) begin
            `uvm_fatal(this.get_full_name(), "\n\tCanno convet reg model to correct type");
        end

        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            this.eth_to_dma[it].regmodel_set(m_regmodel.stream[it]);
        end
    endfunction

    function bit used();
        return super.used();
    endfunction

    function void write_reset(uvm_reset::sequence_item tr);
        if (tr.reset == 1'b1) begin
            for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
                eth_to_dma[it].reset();
                in_eth_mvb[it].flush();
                in_eth_mfb[it].flush();
            end

            for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
                dma_hdr_fifo[it].delete();
                in_dma_mvb[it].flush();
                in_dma_mfb[it].flush();
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
        uvm_common::model_item#(uvm_logic_vector::sequence_item#(ETH_RX_HDR_WIDTH))                item;
        uvm_common::model_item#(uvm_app_core::packet_header #(DMA_HDR_META_WIDTH, DMA_RX_CHANNELS, DMA_PKT_MTU)) dma_hdr;

        forever begin
            in_eth_mvb[index].get(item);
            {timestamp, timestamp_vld, hitmac, hitmac_vld, multicast, error, port, length} = item.item.data;

            dma_hdr = new();
            dma_hdr.time_array_add(item.start);
            dma_hdr.item = new();
            dma_hdr.item.meta        = '0;
            dma_hdr.item.channel     = eth_to_dma[index].port_get(port%ETH_CHANNELS);
            dma_hdr.item.packet_size = length;
            dma_hdr.item.discard     = 0;

            if (DMA_STREAMS == 1) begin
                out_dma_mvb[0].write(dma_hdr);
            end else begin
                out_dma_mvb[index].write(dma_hdr);
            end
        end
    endtask

    task run_eth_mfb(int unsigned index);
        uvm_common::model_item#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) packet;

        forever begin
            in_eth_mfb[index].get(packet);
            if (DMA_STREAMS == 1) begin
                out_dma_mfb[0].write(packet);
            end else begin
                out_dma_mfb[index].write(packet);
            end
        end
    endtask

    task run_dma_mvb(int unsigned index);
        logic [$clog2(DMA_PKT_MTU+1)-1:0] length;
        logic [DMA_HDR_META_WIDTH-1:0]    meta;
        logic [$clog2(DMA_TX_CHANNELS)-1:0] channel;
        int unsigned eth_channel;

        uvm_common::model_item#(uvm_logic_vector::sequence_item#(DMA_RX_MVB_WIDTH)) header;
        uvm_common::model_item#(uvm_app_core::packet_header #(0, 2**ETH_TX_CHANNEL_WIDTH, 2**ETH_TX_LENGTH_WIDTH-1)) eth_hdr;

        forever begin
            in_dma_mvb[index].get(header);

            {channel, meta, length} = header.item.data;
            eth_channel = ((index * DMA_TX_CHANNELS) + channel)/((DMA_STREAMS*DMA_TX_CHANNELS)/(ETH_STREAMS*ETH_CHANNELS));

            //create DMA header
            eth_hdr = new();
            eth_hdr.time_array_add(header.start);
            eth_hdr.item  = new();
            eth_hdr.item.packet_size = length;
            eth_hdr.item.channel = eth_channel; 
            eth_hdr.item.discard = 1'b0;

            dma_hdr_fifo[index].push_back(header);
            out_eth_mvb[eth_channel/ETH_CHANNELS].write(eth_hdr);
        end
    endtask

    task run_dma_mfb(int unsigned index);
        logic [$clog2(DMA_PKT_MTU+1)-1:0] length;
        logic [DMA_HDR_META_WIDTH-1:0]    meta;
        logic [$clog2(DMA_TX_CHANNELS)-1:0] channel;
        int unsigned eth_channel;
        uvm_common::model_item#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) packet;
        uvm_common::model_item#(uvm_logic_vector::sequence_item#(DMA_RX_MVB_WIDTH)) hdr;

        forever begin
            in_dma_mfb[index].get(packet);

            wait(dma_hdr_fifo[index].size() != 0);
            hdr = dma_hdr_fifo[index].pop_front();
            {channel, meta, length} = hdr.item.data;
            eth_channel = ((index * DMA_TX_CHANNELS) + channel)/((DMA_STREAMS*DMA_TX_CHANNELS)/(ETH_STREAMS*ETH_CHANNELS));

            if (length != packet.item.size()) begin
                string msg;
                $sformat(msg, "\n\tDMA TO ETH[%0d] Header is desynchronize from packet\nHeader input time %0dns\n\t%s\nPacket input time %0dns\n\t%s", index, hdr.time_last()/1ns, hdr.item.convert2string(), packet.time_last()/1ns, packet.item.convert2string());
                `uvm_fatal(this.get_full_name(), msg);
            end

            out_eth_mfb[eth_channel/ETH_CHANNELS].write(packet);
        end
    endtask

    task run_eth(uvm_phase phase, int unsigned index);
        fork
           run_eth_mfb(index);
           run_eth_mvb(index);
        join
    endtask

    task run_dma(uvm_phase phase, int unsigned index);
         fork
           run_dma_mfb(index);
           run_dma_mvb(index);
        join
   endtask

    function void report_phase(uvm_phase phase);
    endfunction
endclass
