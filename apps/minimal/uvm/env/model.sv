/*
 * file       : model_minimal.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Model create expectated output from input.
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class model #(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_app_core::model #(ETH_STREAMS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, ITEM_WIDTH);
    `uvm_component_param_utils(uvm_app_core_minimal::model#(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    //LOCAL VARIABLES
    localparam APP_RX_CHANNELS = DMA_RX_CHANNELS/(ETH_STREAMS/DMA_STREAMS);
    protected uvm_channel_router::model#(ETH_CHANNELS, APP_RX_CHANNELS, 2, 1) eth_to_dma[ETH_STREAMS];

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);
            eth_to_dma[it] = uvm_channel_router::model#(ETH_CHANNELS, APP_RX_CHANNELS, 2, 1)::type_id::create({"eth_to_dma_index_", it_num}, this);
        end
    endfunction


    virtual function void regmodel_set(uvm_app_core::regmodel m_regmodel_base);
        uvm_app_core_minimal::regmodel #(ETH_STREAMS, ETH_CHANNELS, DMA_STREAMS, DMA_RX_CHANNELS) m_regmodel;

        if ($cast(m_regmodel, m_regmodel_base) != 1) begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot convert reg model to correct type");
        end

        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            this.eth_to_dma[it].regmodel_set(m_regmodel.stream[it]);
        end
    endfunction

    function bit used();
        bit ret = 0;

        ret |= super.used();
    endfunction

    virtual function void reset();
        super.reset();
        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            eth_to_dma[it].reset();
        end
    endfunction

    task run_eth(uvm_phase phase, int unsigned index);
        uvm_app_core_top_agent::sequence_eth_item#(2**8, 16, ITEM_WIDTH) item;
        uvm_app_core::packet #(DMA_HDR_META_WIDTH, DMA_RX_CHANNELS, DMA_PKT_MTU, ITEM_WIDTH) packet;

        forever begin
            //get item
            eth_rx[index].get(item);

            packet = uvm_app_core::packet #(DMA_HDR_META_WIDTH, DMA_RX_CHANNELS, DMA_PKT_MTU, ITEM_WIDTH)::type_id::create("packet", this);
            packet.start = item.start;
            packet.data = item.data;
            packet.meta = '0;
            if (DMA_STREAMS != ETH_STREAMS) begin
                packet.channel = (index*APP_RX_CHANNELS) + eth_to_dma[index].port_get(item.channel%ETH_CHANNELS);
            end else begin
                packet.channel = eth_to_dma[index].port_get(item.channel%ETH_CHANNELS);
            end
            //packet.packet_size = item.data.size();
            packet.discard     = 0;

            if (DMA_STREAMS == 1) begin
                dma_tx[0].write(packet);
            end else begin
                dma_tx[index].write(packet);
            end
        end
    endtask

    task run_dma(uvm_phase phase, int unsigned index);
        int unsigned eth_channel;
        uvm_app_core_top_agent::sequence_dma_item#(DMA_RX_CHANNELS, $clog2(DMA_PKT_MTU+1), DMA_HDR_META_WIDTH, ITEM_WIDTH) item;

        uvm_app_core::packet #(0, 2**ETH_TX_CHANNEL_WIDTH, 2**ETH_TX_LENGTH_WIDTH-1, ITEM_WIDTH) packet;
        //uvm_app_core::packet_header #(0, 2**ETH_TX_CHANNEL_WIDTH, 2**ETH_TX_LENGTH_WIDTH-1) packet_hdr;
        //uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) packet_data;

        forever begin

            dma_rx[index].get(item);

            packet = uvm_app_core::packet #(0, 2**ETH_TX_CHANNEL_WIDTH, 2**ETH_TX_LENGTH_WIDTH-1, ITEM_WIDTH)::type_id::create("packet", this);
            packet.start = item.start;
            eth_channel = ((index * DMA_TX_CHANNELS) + item.channel)/((DMA_STREAMS*DMA_TX_CHANNELS)/(ETH_STREAMS*ETH_CHANNELS));
            packet.channel = eth_channel;
            packet.discard = 1'b0;
            packet.data  = item.data;

            eth_tx[eth_channel/ETH_CHANNELS].write(packet);

        end
    endtask

    function void report_phase(uvm_phase phase);
    endfunction
endclass
