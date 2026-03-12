/*
 * file       : sequence.sv
 * Copyright (C) 2024 CESNET z. s. p. o.
 * description: verification sequence
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class sequence_main #(
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
    `ndk_object_param_utils(
        uvm_app_core::sequence_main #(
            DMA_TX_CHANNELS,
            DMA_RX_CHANNELS,
            DMA_PKT_MTU,
            DMA_HDR_META_WIDTH,
            DMA_STREAMS,
            ETH_TX_HDR_WIDTH,
            MFB_ITEM_WIDTH,
            ETH_STREAMS,
            REGIONS,
            MFB_REG_SIZE,
            MFB_BLOCK_SIZE,
            MEM_PORTS,
            MEM_ADDR_WIDTH,
            MEM_DATA_WIDTH,
            MEM_BURST_WIDTH
        ),
        $sformatf("uvm_app_core::sequence_main#(%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d)",
            DMA_TX_CHANNELS,
            DMA_RX_CHANNELS,
            DMA_PKT_MTU,
            DMA_HDR_META_WIDTH,
            DMA_STREAMS,
            ETH_TX_HDR_WIDTH,
            MFB_ITEM_WIDTH,
            ETH_STREAMS,
            REGIONS,
            MFB_REG_SIZE,
            MFB_BLOCK_SIZE,
            MEM_PORTS,
            MEM_ADDR_WIDTH,
            MEM_DATA_WIDTH,
            MEM_BURST_WIDTH
        )
    )

    localparam int unsigned DMA_RX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_RX_CHANNELS);
    localparam int unsigned DMA_TX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_TX_CHANNELS) + 1;
    typedef uvm_app_core_top_agent::sequence_eth_item #(
        2**8,
        16,
        MFB_ITEM_WIDTH
    ) sequence_item_eth_rx;
    typedef uvm_app_core_top_agent::sequence_dma_item #(
        DMA_RX_CHANNELS,
        $clog2(DMA_PKT_MTU+1),
        DMA_HDR_META_WIDTH,
        MFB_ITEM_WIDTH
    ) sequence_item_dma_rx;

    `uvm_declare_p_sequencer(
        uvm_app_core::sequencer #(
            DMA_RX_CHANNELS,
            DMA_PKT_MTU,
            DMA_HDR_META_WIDTH,
            DMA_STREAMS,
            MFB_ITEM_WIDTH,
            ETH_STREAMS,
            MEM_PORTS,
            MEM_ADDR_WIDTH,
            MEM_DATA_WIDTH,
            MEM_BURST_WIDTH
        )
    )

    protected uvm_common::sequence_cfg_signal rx_status;
    protected logic [ETH_STREAMS-1:0] event_eth_rx_end;
    protected logic [DMA_STREAMS-1:0] event_dma_rx_end;
    rand time time_start;
    bit [128-1:0] conf_ipv6[];
    bit [32-1:0]  conf_ipv4[];
    int unsigned min_random_count;
    int unsigned max_random_count;
    int unsigned pkt_size_min;
    int unsigned pkt_size_max;

    time run_time_min;
    time run_time_max;

    function new (string name = "uvm_app_core::sequencer");
        super.new(name);
        rx_status = new();
        min_random_count = 50;
        max_random_count = 150;
        pkt_size_min = 60;
        pkt_size_max = DMA_PKT_MTU;
        run_time_min = 40us;
        run_time_max = 400us;
    endfunction


    virtual task eth_rx_sequence(int unsigned index);
        uvm_app_core::sequence_library_eth#(2**8, 16, MFB_ITEM_WIDTH) packet_seq;
        config_sequence_eth seq_cfg;

        seq_cfg = new();
        seq_cfg.time_start = time_start;
        seq_cfg.ipv4_addresses = conf_ipv4;
        seq_cfg.ipv6_addresses = conf_ipv6;
        seq_cfg.array_size_set(pkt_size_min, pkt_size_max);
        packet_seq = uvm_app_core::sequence_library_eth #(
            2**8,
            16,
            MFB_ITEM_WIDTH
        )::type_id::create("packet_seq", p_sequencer.m_eth_rx[index]);
        packet_seq.init_sequence(seq_cfg);

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_eth_rx[index], "", "state", rx_status);
        while (!rx_status.stopped()) begin
            assert(packet_seq.randomize());
            packet_seq.start(p_sequencer.m_eth_rx[index]);
        end

        event_eth_rx_end[index] = 1'b0;
    endtask


    virtual task dma_rx_sequence(int unsigned index);
        uvm_app_core_top_agent::sequence_base#(sequence_item_dma_rx) packet_seq;

        packet_seq = uvm_app_core_top_agent::sequence_base #(sequence_item_dma_rx)::type_id::create(
            "packet_seq",
            p_sequencer.m_dma_rx[index]
        );

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_dma_rx[index], "", "state", rx_status);
        while (!rx_status.stopped()) begin
            assert(packet_seq.randomize());
            packet_seq.start(p_sequencer.m_dma_rx[index]);
        end

        event_dma_rx_end[index] = 1'b0;
    endtask


    task body;
        time run_time;
        rx_status.clear();
        event_eth_rx_end = '{ETH_STREAMS {1'b1}};
        event_dma_rx_end = '{DMA_STREAMS {1'b1}};

        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            fork
                automatic int index = it;
                dma_rx_sequence(index);
            join_none;
        end

        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            fork
                automatic int index = it;
                eth_rx_sequence(index);
            join_none;
        end

        assert(std::randomize(run_time) with {run_time inside {[run_time_min:run_time_max]};}) else begin
            `uvm_fatal(m_sequencer.get_full_name(),
                $sformatf("\n\tCannot randomize run time [%0dns:%0dns]", run_time_min,run_time_max)
            );
        end
        #(run_time);
        rx_status.send_stop();

        wait(event_dma_rx_end === 0);
        wait(event_eth_rx_end === 0);
    endtask

endclass


