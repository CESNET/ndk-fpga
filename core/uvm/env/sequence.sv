/*
 * file       : sequence.sv
 * Copyright (C) 2024 CESNET z. s. p. o.
 * description: verification sequence 
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class sequence_main#(
    int unsigned DMA_TX_CHANNELS,
    int unsigned DMA_RX_CHANNELS,
    int unsigned DMA_PKT_MTU,
    int unsigned DMA_HDR_META_WIDTH,
    int unsigned DMA_STREAMS,
    int unsigned ETH_TX_HDR_WIDTH,
    int unsigned MFB_ITEM_WIDTH,
    int unsigned ETH_STREAMS,
    int unsigned REGIONS,
    int unsigned MFB_REG_SIZE,
    int unsigned MFB_BLOCK_SIZE,
    int unsigned MEM_PORTS,
    int unsigned MEM_ADDR_WIDTH,
    int unsigned MEM_DATA_WIDTH,
    int unsigned MEM_BURST_WIDTH
) extends uvm_sequence;
    `uvm_object_param_utils(uvm_app_core::sequence_main#(DMA_TX_CHANNELS, DMA_RX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,
    MFB_ITEM_WIDTH, ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH))

    localparam DMA_RX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_RX_CHANNELS);
    localparam DMA_TX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_TX_CHANNELS) + 1;
    typedef uvm_app_core_top_agent::sequence_eth_item#(2**8, 16, MFB_ITEM_WIDTH)                                                   sequence_item_eth_rx;
    typedef uvm_app_core_top_agent::sequence_dma_item#(DMA_RX_CHANNELS, $clog2(DMA_PKT_MTU+1), DMA_HDR_META_WIDTH, MFB_ITEM_WIDTH) sequence_item_dma_rx;

    `uvm_declare_p_sequencer(uvm_app_core::sequencer#(DMA_TX_CHANNELS, DMA_RX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                                ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH))

    protected uvm_common::sequence_cfg_signal rx_status;
    protected uvm_common::sequence_cfg_signal tx_status;
    //protected logic tx_done;
    protected logic [ETH_STREAMS-1:0] event_eth_rx_end;
    protected logic [DMA_STREAMS-1:0] event_dma_rx_end;
    rand time time_start;
    logic [128-1:0] conf_ipv6[];
    logic [32-1:0]  conf_ipv4[];


    function new (string name = "uvm_app_core::sequencer");
        super.new(name);
        tx_status = new();
        rx_status = new();
    endfunction

    virtual task eth_tx_sequence(int unsigned index);
        uvm_mfb::sequence_lib_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH) mfb_seq;

        mfb_seq = uvm_mfb::sequence_lib_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH)::type_id::create("mfb_eth_tx_seq", p_sequencer.m_eth_tx[index]);
        mfb_seq.init_sequence();
        mfb_seq.min_random_count = 50;
        mfb_seq.max_random_count = 150;

        //RUN ETH
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_eth_tx[index], "", "state", tx_status);
        while (!tx_status.stopped()) begin
            mfb_seq.randomize();
            mfb_seq.start(p_sequencer.m_eth_tx[index]);
        end

    endtask

    virtual task dma_tx_sequence(int unsigned index);
        uvm_mfb::sequence_lib_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) mfb_seq;
        uvm_mvb::sequence_lib_tx#(REGIONS, DMA_TX_MVB_WIDTH)                                mvb_seq;

        mvb_seq = uvm_mvb::sequence_lib_tx#(REGIONS, DMA_TX_MVB_WIDTH)::type_id::create("mvb_dma_tx_seq", p_sequencer.m_dma_mvb_tx[index]);
        mvb_seq.min_random_count = 50;
        mvb_seq.max_random_count = 150;
        mvb_seq.init_sequence();

        mfb_seq = uvm_mfb::sequence_lib_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create("mfb_dma_tx_seq", p_sequencer.m_dma_mfb_tx[index]);
        mfb_seq.min_random_count = 50;
        mfb_seq.max_random_count = 150;
        mfb_seq.init_sequence();


        //RUN ETH
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_dma_mvb_tx[index], "", "state", tx_status);
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_dma_mfb_tx[index], "", "state", tx_status);
        fork
            while (!tx_status.stopped()) begin
                //mvb_seq.set_starting_phase(phase);
                void'(mvb_seq.randomize());
                mvb_seq.start(p_sequencer.m_dma_mvb_tx[index]);
            end
            while (!tx_status.stopped()) begin
                //mfb_seq.set_starting_phase(phase);
                void'(mfb_seq.randomize());
                mfb_seq.start(p_sequencer.m_dma_mfb_tx[index]);
            end
        join;
    endtask



    virtual task eth_rx_sequence(int unsigned index);
        uvm_app_core::sequence_library_eth#(2**8, 16, MFB_ITEM_WIDTH) packet_seq;
        config_sequence_eth seq_cfg;
        int unsigned it;

        seq_cfg = new();
        seq_cfg.time_start = time_start;
        seq_cfg.ipv4_addresses = conf_ipv4;
        seq_cfg.ipv6_addresses = conf_ipv6;
        packet_seq = uvm_app_core::sequence_library_eth#(2**8, 16, MFB_ITEM_WIDTH)::type_id::create("mfb_rx_seq", p_sequencer.m_eth_rx[index]);
        packet_seq.init_sequence(seq_cfg);

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_eth_rx[index], "", "state", rx_status);
        it = 0;
        while (it < 10 && !rx_status.stopped()) begin
            assert(packet_seq.randomize());
            packet_seq.start(p_sequencer.m_eth_rx[index]);
            it++;
        end

        event_eth_rx_end[index] = 1'b0;
    endtask


    virtual task dma_rx_sequence(int unsigned index);
        uvm_app_core_top_agent::sequence_base#(sequence_item_dma_rx) packet_seq;
        int unsigned it;

        packet_seq = uvm_app_core_top_agent::sequence_base#(sequence_item_dma_rx)::type_id::create("mfb_rx_seq", p_sequencer.m_dma_rx[index]);

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_dma_rx[index], "", "state", rx_status);
        it = 0;
        while (it < 10 && !rx_status.stopped()) begin
            assert(packet_seq.randomize());
            packet_seq.start(p_sequencer.m_dma_rx[index]);
            it++;
        end

        event_dma_rx_end[index] = 1'b0;
    endtask


    task body;
        rx_status.clear();
        tx_status.clear();
        event_eth_rx_end = '{ETH_STREAMS {1'b1}};
        event_dma_rx_end = '{DMA_STREAMS {1'b1}};

        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            fork
                automatic int index = it;
                dma_rx_sequence(index);
                dma_tx_sequence(index);
            join_none;
        end

        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            fork
                automatic int index = it;
                eth_rx_sequence(index);
                eth_tx_sequence(index);
            join_none;
        end

        wait (event_dma_rx_end != '1 || event_eth_rx_end != '1);
        rx_status.send_stop();

        wait(event_dma_rx_end === 0);
        wait(event_eth_rx_end === 0);
        tx_status.send_stop();
    endtask

endclass


class sequence_stop#(
    int unsigned DMA_TX_CHANNELS,
    int unsigned DMA_RX_CHANNELS,
    int unsigned DMA_PKT_MTU,
    int unsigned DMA_HDR_META_WIDTH,
    int unsigned DMA_STREAMS,
    int unsigned ETH_TX_HDR_WIDTH,
    int unsigned MFB_ITEM_WIDTH,
    int unsigned ETH_STREAMS,
    int unsigned REGIONS,
    int unsigned MFB_REG_SIZE,
    int unsigned MFB_BLOCK_SIZE,
    int unsigned MEM_PORTS,
    int unsigned MEM_ADDR_WIDTH,
    int unsigned MEM_DATA_WIDTH,
    int unsigned MEM_BURST_WIDTH
) extends uvm_app_core::sequence_main#(DMA_TX_CHANNELS, DMA_RX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                    ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH);
    `uvm_object_param_utils(uvm_app_core::sequence_stop#(DMA_TX_CHANNELS, DMA_RX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH, MFB_ITEM_WIDTH,
                    ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH))


    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
    endfunction

    function void done_set();
        tx_status.send_stop();
    endfunction

    task body;
        tx_status.clear();
        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            fork
                automatic int index = it;
                dma_tx_sequence(index);
            join_none;
        end

        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            fork
                automatic int index = it;
                eth_tx_sequence(index);
            join_none;
        end

        while (tx_status.stopped() == 0) begin
            #(30ns);
        end
    endtask

endclass

