/*
 * file       : test.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description:  base test 
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class full_speed#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends
      base#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH);

    typedef uvm_component_registry#(test::full_speed#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
                                                REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH),
                                               "test::full_speed") type_id;


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
        m_env.delay_max_set(1ms);
    endfunction

    static function type_id get_type();
        return type_id::get();
    endfunction

    function string get_type_name();
        return get_type().get_type_name();
    endfunction

    function new (string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task eth_tx_sequence(uvm_phase phase, int unsigned index);
        uvm_mfb::sequence_lib_tx_speed#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH) mfb_seq;

        mfb_seq = uvm_mfb::sequence_lib_tx_speed#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH)::type_id::create("mfb_eth_tx_seq", this);
        mfb_seq.init_sequence();
        mfb_seq.min_random_count = 10;
        mfb_seq.max_random_count = 20;

        //RUN ETH
        forever begin
            //mfb_seq.set_starting_phase(phase);
            mfb_seq.randomize();
            mfb_seq.start(m_env.m_eth_mfb_tx[index].m_sequencer);
        end
    endtask

    virtual task eth_rx_sequence(uvm_phase phase, int unsigned index);
        super.eth_rx_sequence(phase, index);
    endtask

    virtual task dma_tx_sequence(uvm_phase phase, int unsigned index);
        uvm_mfb::sequence_lib_tx_speed#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) mfb_seq;
        uvm_mvb::sequence_lib_tx_speed#(REGIONS, DMA_TX_MVB_WIDTH)                                mvb_seq;

        mfb_seq = uvm_mfb::sequence_lib_tx_speed#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create("mfb_dma_tx_seq", this);
        mfb_seq.init_sequence();
        mfb_seq.min_random_count = 10;
        mfb_seq.max_random_count = 20;

        mvb_seq = uvm_mvb::sequence_lib_tx_speed#(REGIONS, DMA_TX_MVB_WIDTH)::type_id::create("mvb_dma_tx_seq", this);
        mvb_seq.init_sequence();
        mvb_seq.min_random_count = 10;
        mvb_seq.max_random_count = 20;

        //RUN ETH
        fork
            forever begin
                //mvb_seq.set_starting_phase(phase);
                void'(mvb_seq.randomize());
                mvb_seq.start(m_env.m_dma_mvb_tx[index].m_sequencer);
            end
            forever begin
                //mfb_seq.set_starting_phase(phase);
                void'(mfb_seq.randomize());
                mfb_seq.start(m_env.m_dma_mfb_tx[index].m_sequencer);
            end
        join_none;
    endtask

    virtual task dma_rx_sequence(uvm_phase phase, int unsigned index);
        super.dma_rx_sequence(phase, index);
    endtask
endclass
