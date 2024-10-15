/*
 * file       : test.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description:  base test
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_speed#(
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
    `uvm_object_param_utils(test::sequence_speed#(DMA_TX_CHANNELS, DMA_RX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
            ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
    endfunction


    virtual task eth_tx_sequence(int unsigned index);
        uvm_mfb::sequence_lib_tx_speed#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH) mfb_seq;

        mfb_seq = uvm_mfb::sequence_lib_tx_speed#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH)::type_id::create("mfb_eth_tx_seq", p_sequencer.m_eth_tx[index]);
        mfb_seq.init_sequence();
        mfb_seq.min_random_count = 10;
        mfb_seq.max_random_count = 20;

        //RUN ETH
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_eth_tx[index], "", "state", tx_status);
        while (!tx_status.stopped()) begin
            mfb_seq.randomize();
            mfb_seq.start(p_sequencer.m_eth_tx[index]);
        end
    endtask

    virtual task dma_tx_sequence(int unsigned index);
        uvm_mfb::sequence_lib_tx_speed#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) mfb_seq;
        uvm_mvb::sequence_lib_tx_speed#(REGIONS, DMA_TX_MVB_WIDTH)                                mvb_seq;

        mfb_seq = uvm_mfb::sequence_lib_tx_speed#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create("mfb_dma_tx_seq", p_sequencer.m_dma_mfb_tx[index]);
        mfb_seq.init_sequence();
        mfb_seq.min_random_count = 10;
        mfb_seq.max_random_count = 20;

        mvb_seq = uvm_mvb::sequence_lib_tx_speed#(REGIONS, DMA_TX_MVB_WIDTH)::type_id::create("mvb_dma_tx_seq", p_sequencer.m_dma_mvb_tx[index]);
        mvb_seq.init_sequence();
        mvb_seq.min_random_count = 10;
        mvb_seq.max_random_count = 20;

        //RUN ETH
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_dma_mvb_tx[index], "", "state", tx_status);
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_dma_mfb_tx[index], "", "state", tx_status);
        fork
            while (!tx_status.stopped()) begin
                //mfb_seq.set_starting_phase(phase);
                void'(mfb_seq.randomize());
                mfb_seq.start(p_sequencer.m_dma_mfb_tx[index]);
            end
            while (!tx_status.stopped()) begin
                //mvb_seq.set_starting_phase(phase);
                void'(mvb_seq.randomize());
                mvb_seq.start(p_sequencer.m_dma_mvb_tx[index]);
            end
        //join_none;
        join;
    endtask
endclass


class full_speed#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends
      base#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH);

    typedef uvm_component_registry#(test::full_speed#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
                                                REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH),
                                               "test::full_speed") type_id;

    function new (string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    static function type_id get_type();
        return type_id::get();
    endfunction

    function string get_type_name();
        return get_type().get_type_name();
    endfunction

    function void build_phase(uvm_phase phase);
        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            uvm_logic_vector_array_mfb::sequence_lib_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::set_inst_override(uvm_logic_vector_array_mfb::sequence_lib_rx_speed#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::get_type(),
             {this.get_full_name(), ".m_env.m_eth_mfb_rx_", it_num ,".*"});

             uvm_logic_vector_mvb::sequence_lib_rx#(REGIONS, ETH_RX_HDR_WIDTH)::type_id::set_inst_override(uvm_logic_vector_mvb::sequence_lib_speed_rx#(REGIONS, ETH_RX_HDR_WIDTH)::get_type(),
             {this.get_full_name(), ".m_env.m_eth_mvb_rx_", it_num,".*"});
        end

        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            uvm_logic_vector_array_mfb::sequence_lib_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::set_inst_override(uvm_logic_vector_array_mfb::sequence_lib_rx_speed#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::get_type(),
             {this.get_full_name(), ".m_env.m_dma_mfb_rx_", it_num,".*"});

            uvm_logic_vector_mvb::sequence_lib_rx#(REGIONS, DMA_RX_MVB_WIDTH)::type_id::set_inst_override(uvm_logic_vector_mvb::sequence_lib_speed_rx#(REGIONS, DMA_RX_MVB_WIDTH)::get_type(),
             {this.get_full_name(), ".m_env.m_dma_mvb_rx_", it_num,".*"});

            //.mfb_seq
        end

        super.build_phase(phase);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        m_env.delay_max_set(10ms, 10ms);
    endfunction

    virtual task run_phase(uvm_phase phase);
        uvm_app_core::sequence_tsu  tsu_seq;
        test::sequence_speed#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                    ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH) main_seq;
        uvm_app_core::sequence_stop#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                    ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH) stop_seq;
        time end_time;
        int rdy2end;

        main_seq = test::sequence_speed#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                    ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH)::type_id::create("main_seq", m_env.m_sequencer);
        stop_seq = uvm_app_core::sequence_stop#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                    ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH)::type_id::create("stop_seq", m_env.m_sequencer);
        phase.raise_objection(this);

        // RUN RESET
        fork
            run_reset(phase);
        join_none;

        // RUN TSU
        tsu_seq = uvm_app_core::sequence_tsu::type_id::create("tsu_seq", m_env.m_tsu.m_sequencer);
        tsu_seq.randomize();
        fork
            tsu_seq.start(m_env.m_tsu.m_sequencer);
        join_none;

        ////configure egent
        wait(event_reset == 1'b0);
        for (int unsigned it = 0; it < 3; it++) begin

            //RUN RIVER SEQUENCE ONLY IF RESET IS NOT SET
            dirver_sequence();
            #(200ns);

            end_time = $time() + 400us;
            while (end_time > $time()) begin
            //for (int unsigned it = 0; it < 10; it++) begin
                assert(main_seq.randomize()) else `uvm_fatal(m_env.m_sequencer.get_full_name(), "\n\tCannot randomize main sequence");
                main_seq.start(m_env.m_sequencer);
                main_seq.time_start = tsu_seq.time_start;
            end

            assert(stop_seq.randomize()) else `uvm_fatal(m_env.m_sequencer.get_full_name(), "\n\tCannot randomize main sequence");

            fork
                stop_seq.start(m_env.m_sequencer);
            join_none;

            end_time = $time() + 50ms; // Prevents verification from freezing after a very long time!
            rdy2end = 0;
            while (end_time > $time() && rdy2end < 5) begin
                // The check of the number of incomplete packets in the verification must pass repeatedly!
                if (m_env.used() == 0) begin
                    rdy2end++;
                end else begin
                    rdy2end = 0;
                end
                #(1us);
            end
            if (m_env.used() != 0) begin
                `uvm_warning(this.get_full_name(), $sformatf("\n\tUSED(%0d) sould be zero.\n\tDuring reconfiguration, There is some data in design", m_env.used()));
            end

            stop_seq.done_set();
        end

        phase.drop_objection(this);
    endtask
endclass
