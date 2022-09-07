/*
 * file       : test.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description:  base test 
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class mfb_rx_speed#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) extends uvm_logic_vector_array_mfb::sequence_lib_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
  `uvm_object_param_utils(    test::mfb_rx_speed#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))
  `uvm_sequence_library_utils(test::mfb_rx_speed#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    function new(string name = "mfb_rx_speed");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(uvm_logic_vector_array_mfb::config_sequence param_cfg = null);
        if (param_cfg == null) begin
            this.cfg = new();
        end else begin
            this.cfg = param_cfg;
        end
        this.add_sequence(uvm_logic_vector_array_mfb::sequence_full_speed_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
        this.add_sequence(uvm_logic_vector_array_mfb::sequence_stop_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
    endfunction
endclass

class mfb_lib_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) extends uvm_sequence_library#(uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH));
  `uvm_object_param_utils(    test::mfb_lib_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))
  `uvm_sequence_library_utils(test::mfb_lib_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

  function new(string name = "");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence();
        this.add_sequence(uvm_mfb::sequence_full_speed_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
        this.add_sequence(uvm_mfb::sequence_stop_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
    endfunction
endclass

class mvb_lib_tx#(ITEMS, ITEM_WIDTH) extends uvm_sequence_library#(uvm_mvb::sequence_item#(ITEMS, ITEM_WIDTH));
  `uvm_object_param_utils(    test::mvb_lib_tx#(ITEMS, ITEM_WIDTH))
  `uvm_sequence_library_utils(test::mvb_lib_tx#(ITEMS, ITEM_WIDTH))

    function new(string name = "");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence();
        this.add_sequence(uvm_mvb::sequence_full_speed_tx#(ITEMS, ITEM_WIDTH)::get_type());
        this.add_sequence(uvm_mvb::sequence_stop_tx#(ITEMS, ITEM_WIDTH)::get_type());
    endfunction
endclass

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

            uvm_logic_vector_array_mfb::sequence_lib_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::set_inst_override(mfb_rx_speed#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::get_type(),
             {this.get_full_name(), ".m_env.m_eth_mfb_rx_", it_num ,".*"});
        end

        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            uvm_logic_vector_array_mfb::sequence_lib_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::set_inst_override(mfb_rx_speed#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::get_type(),
             {this.get_full_name(), ".m_env.m_dma_mfb_rx_", it_num,".*"});
            //.mfb_seq
        end

        super.build_phase(phase);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        m_env.delay_max_set(200ns);
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
        mfb_lib_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH) mfb_seq;

        mfb_seq = mfb_lib_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH)::type_id::create("mfb_eth_tx_seq", this);
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
        uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH) mfb_seq;

        mfb_seq = uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH)::type_id::create("mfb_rx_seq", this);
        mfb_seq.min_random_count = 10;
        mfb_seq.max_random_count = 20;
        mfb_seq.init_sequence();

        //SEND PACKETS
        //mfb_seq.set_starting_phase(phase);
        assert(mfb_seq.randomize());
        mfb_seq.start(m_eth_agent[index].m_sequencer);
        event_eth_rx_end[index] = 1'b1;
    endtask

    virtual task dma_tx_sequence(uvm_phase phase, int unsigned index);
        mfb_lib_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) mfb_seq;
        mvb_lib_tx#(REGIONS, DMA_TX_MVB_WIDTH)                                mvb_seq;

        mfb_seq = mfb_lib_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create("mfb_dma_tx_seq", this);
        mfb_seq.init_sequence();
        mfb_seq.min_random_count = 10;
        mfb_seq.max_random_count = 20;

        mvb_seq = mvb_lib_tx#(REGIONS, DMA_TX_MVB_WIDTH)::type_id::create("mvb_dma_tx_seq", this);
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
        uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH) mfb_seq;

        mfb_seq = uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH)::type_id::create("mfb_dma_rx_seq", this);
        mfb_seq.init_sequence();
        mfb_seq.min_random_count = 10;
        mfb_seq.max_random_count = 20;

        //SEND PACKETS
        //mfb_seq.set_starting_phase(phase);
        assert(mfb_seq.randomize());
        mfb_seq.start(m_dma_agent[index].m_sequencer);
        event_dma_rx_end[index] = 1'b1;
    endtask
endclass
