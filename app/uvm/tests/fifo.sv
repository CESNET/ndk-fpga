/*
 * file       : test.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description:  base test 
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class sequence_mfb_full_speed_rx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends uvm_logic_vector_array_mfb::sequence_full_speed_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `uvm_object_param_utils(test::sequence_mfb_full_speed_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    function new(string name = "test::sequence_mfb_full_speed_rx");
        super.new(name);
        hl_transactions_min = 1000;
        hl_transactions_max = 20000;
    endfunction
endclass


class sequence_mfb_stop_rx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends uvm_logic_vector_array_mfb::sequence_stop_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `uvm_object_param_utils(test::sequence_mfb_stop_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    function new(string name = "test::sequence_mfb_stop_rx");
        super.new(name);
        hl_transactions_min = 1000;
        hl_transactions_max = 20000;
    endfunction
endclass


class sequence_lib__mfb_rx_fifo #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends uvm_logic_vector_array_mfb::sequence_lib_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
  `uvm_object_param_utils(    test::sequence_lib__mfb_rx_fifo#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))
  `uvm_sequence_library_utils(test::sequence_lib__mfb_rx_fifo#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

  function new(string name = "test::sequence_lib__mfb_rx_fifo");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(uvm_logic_vector_array_mfb::config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(test::sequence_mfb_full_speed_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
        this.add_sequence(test::sequence_mfb_stop_rx       #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
    endfunction
endclass

class sequence_mvb_full_speed_rx #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_logic_vector_mvb::sequence_full_speed_rx       #(ITEMS, ITEM_WIDTH);
    `uvm_object_param_utils(test::sequence_mvb_full_speed_rx #(ITEMS, ITEM_WIDTH))

    function new(string name = "test::sequence_mvb_full_speed_rx");
        super.new(name);
        hl_transactions_min = 1000;
        hl_transactions_max = 20000;
    endfunction
endclass


class sequence_mvb_stop_rx #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_logic_vector_mvb::sequence_stop_rx #(ITEMS, ITEM_WIDTH);
    `uvm_object_param_utils(test::sequence_mvb_stop_rx #(ITEMS, ITEM_WIDTH))

    function new(string name = "test::sequence_mvb_stop_rx");
        super.new(name);
        hl_transactions_min = 1000;
        hl_transactions_max = 20000;
    endfunction
endclass


class sequence_lib__mvb_rx_fifo #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_logic_vector_mvb::sequence_lib_rx  #(ITEMS, ITEM_WIDTH);
  `uvm_object_param_utils(    test::sequence_lib__mvb_rx_fifo#(ITEMS, ITEM_WIDTH))
  `uvm_sequence_library_utils(test::sequence_lib__mvb_rx_fifo#(ITEMS, ITEM_WIDTH))

  function new(string name = "test::sequence_lib__mvb_rx_fifo");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(uvm_logic_vector_mvb::config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(test::sequence_mvb_full_speed_rx #(ITEMS, ITEM_WIDTH)::get_type());
        this.add_sequence(test::sequence_mvb_stop_rx       #(ITEMS, ITEM_WIDTH)::get_type());
    endfunction
endclass



class sequence_fifo#(
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
    `uvm_object_param_utils(test::sequence_fifo#(DMA_TX_CHANNELS, DMA_RX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
    endfunction

    virtual task eth_rx_sequence(int unsigned index);
        uvm_app_core::sequence_library_eth#(2**8, 16, MFB_ITEM_WIDTH) packet_seq;
        uvm_app_core::config_sequence_eth seq_cfg;
        int unsigned it;

        seq_cfg = new();
        seq_cfg.time_start = time_start;
        packet_seq = uvm_app_core::sequence_library_eth#(2**8, 16, MFB_ITEM_WIDTH)::type_id::create("mfb_rx_seq", p_sequencer.m_eth_rx[index]);
        packet_seq.init_sequence(seq_cfg);

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_eth_rx[index], "", "state", rx_status);
        it = 0;
        while (it < 200 && !rx_status.stopped()) begin
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
        while (it < 200 && !rx_status.stopped()) begin
            assert(packet_seq.randomize());
            packet_seq.start(p_sequencer.m_dma_rx[index]);
            it++;
        end

        event_dma_rx_end[index] = 1'b0;
    endtask


    virtual task eth_tx_sequence(int unsigned index);
        uvm_mfb::sequence_full_speed_tx #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH) seq_mfb_one;
        uvm_mfb::sequence_stop_tx       #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH) seq_mfb_zero;

        seq_mfb_one  = uvm_mfb::sequence_full_speed_tx #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH)::type_id::create("seq_mfb_one",  p_sequencer.m_eth_tx[index]);
        seq_mfb_one.min_transaction_count =  1000;
        seq_mfb_one.max_transaction_count = 20000;
        seq_mfb_zero = uvm_mfb::sequence_stop_tx       #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH)::type_id::create("seq_mfb_zero", p_sequencer.m_eth_tx[index]);
        seq_mfb_zero.min_transaction_count =  1000;
        seq_mfb_zero.max_transaction_count = 20000;

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_eth_tx[index], "", "state", tx_status);
        while (!tx_status.stopped()) begin
            //mfb_seq.set_starting_phase(phase);
            void'(seq_mfb_one.randomize());
            seq_mfb_one.start(p_sequencer.m_eth_tx[index]);
            void'(seq_mfb_zero.randomize());
            seq_mfb_zero.start(p_sequencer.m_eth_tx[index]);
        end
    endtask


    virtual task dma_tx_sequence(int unsigned index);
        uvm_mfb::sequence_full_speed_tx #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) seq_mfb_one;
        uvm_mfb::sequence_stop_tx       #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) seq_mfb_zero;
        uvm_mvb::sequence_full_speed_tx #(REGIONS, DMA_TX_MVB_WIDTH) seq_mvb_one;
        uvm_mvb::sequence_stop_tx       #(REGIONS, DMA_TX_MVB_WIDTH) seq_mvb_zero;


        seq_mfb_one  = uvm_mfb::sequence_full_speed_tx #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create("seq_mfb_one",  p_sequencer.m_dma_mfb_tx[index]);
        seq_mfb_one.min_transaction_count =  1000;
        seq_mfb_one.max_transaction_count = 20000;
        seq_mfb_zero = uvm_mfb::sequence_stop_tx       #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create("seq_mfb_zero", p_sequencer.m_dma_mfb_tx[index]);
        seq_mfb_zero.min_transaction_count =  1000;
        seq_mfb_zero.max_transaction_count = 20000;


        seq_mvb_one  = uvm_mvb::sequence_full_speed_tx #(REGIONS, DMA_TX_MVB_WIDTH)::type_id::create("seq_mvb_one",  p_sequencer.m_dma_mvb_tx[index]);
        seq_mvb_one.min_transaction_count =  1000;
        seq_mvb_one.max_transaction_count = 20000;
        seq_mvb_zero = uvm_mvb::sequence_stop_tx       #(REGIONS, DMA_TX_MVB_WIDTH)::type_id::create("seq_mvb_zero", p_sequencer.m_dma_mvb_tx[index]);
        seq_mvb_zero.min_transaction_count =  1000;
        seq_mvb_zero.max_transaction_count = 20000;


        //RUN ETH
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_dma_mvb_tx[index], "", "state", tx_status);
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_dma_mfb_tx[index], "", "state", tx_status);
        fork
            while (!tx_status.stopped()) begin
                //mfb_seq.set_starting_phase(phase);
                void'(seq_mfb_one.randomize());
                seq_mfb_one.start(p_sequencer.m_dma_mfb_tx[index]);
                void'(seq_mfb_zero.randomize());
                seq_mfb_zero.start(p_sequencer.m_dma_mfb_tx[index]);
            end
            while (!tx_status.stopped()) begin
                //mvb_seq.set_starting_phase(phase);
                void'(seq_mvb_one.randomize());
                seq_mvb_one.start(p_sequencer.m_dma_mvb_tx[index]);
                void'(seq_mvb_zero.randomize());
                seq_mvb_zero.start(p_sequencer.m_dma_mvb_tx[index]);
            end
        join;
    endtask
endclass


class sequence_fifo_stop#(
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
) extends sequence_fifo#(DMA_TX_CHANNELS, DMA_RX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH);
    `uvm_object_param_utils(test::sequence_fifo_stop#(DMA_TX_CHANNELS, DMA_RX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
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


class fifo#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends
      base#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH);

    typedef uvm_component_registry#(test::fifo#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
                                                REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH),
                                               "test::fifo") type_id;

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

            uvm_logic_vector_array_mfb::sequence_lib_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::set_inst_override(test::sequence_lib__mfb_rx_fifo#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::get_type(),
             {this.get_full_name(), ".m_env.m_eth_mfb_rx_", it_num ,".*"});

             uvm_logic_vector_mvb::sequence_lib_rx#(REGIONS, ETH_RX_HDR_WIDTH)::type_id::set_inst_override(test::sequence_lib__mvb_rx_fifo#(REGIONS, ETH_RX_HDR_WIDTH)::get_type(),
             {this.get_full_name(), ".m_env.m_eth_mvb_rx_", it_num,".*"});
        end

        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            uvm_logic_vector_array_mfb::sequence_lib_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::set_inst_override(test::sequence_lib__mfb_rx_fifo#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::get_type(),
             {this.get_full_name(), ".m_env.m_dma_mfb_rx_", it_num,".*"});

            uvm_logic_vector_mvb::sequence_lib_rx#(REGIONS, DMA_RX_MVB_WIDTH)::type_id::set_inst_override(test::sequence_lib__mvb_rx_fifo#(REGIONS, DMA_RX_MVB_WIDTH)::get_type(),
             {this.get_full_name(), ".m_env.m_dma_mvb_rx_", it_num,".*"});

            //.mfb_seq
        end

        super.build_phase(phase);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        m_env.delay_max_set(1ms);
    endfunction

    virtual task run_phase(uvm_phase phase);
        uvm_app_core::sequence_tsu  tsu_seq;
        test::sequence_fifo#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                            ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH) main_seq;
        test::sequence_fifo_stop#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                            ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH) stop_seq;
        time end_time;

        main_seq = test::sequence_fifo#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                            ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH)::type_id::create("main_seq", m_env.m_sequencer);
        stop_seq = test::sequence_fifo_stop#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
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
        for (int unsigned it = 0; it < 2; it++) begin

            //RUN RIVER SEQUENCE ONLY IF RESET IS NOT SET
            dirver_sequence();
            #(200ns);

            assert(main_seq.randomize()) else `uvm_fatal(m_env.m_sequencer.get_full_name(), "\n\tCannot randomize main sequence");
            main_seq.start(m_env.m_sequencer);
            main_seq.time_start = tsu_seq.time_start;

            assert(stop_seq.randomize()) else `uvm_fatal(m_env.m_sequencer.get_full_name(), "\n\tCannot randomize main sequence");
            fork
                stop_seq.start(m_env.m_sequencer);
            join_none;

            end_time = $time() + 400us;
            while (end_time > $time() && m_env.used() != 0) begin
                #(500ns);
            end
            if (m_env.used() != 0) begin
                `uvm_warning(this.get_full_name(), $sformatf("\n\tUSED(%0d) sould be zero.\n\tDuring reconfiguration, There is some data in design", m_env.used()));
            end

            stop_seq.done_set();
        end

        phase.drop_objection(this);
    endtask
endclass
