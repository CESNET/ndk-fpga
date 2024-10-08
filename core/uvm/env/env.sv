/*
 * file       : env.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: verification eviroment for application core
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class env #(ETH_STREAMS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_app_core::env#(ETH_STREAMS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    localparam DMA_RX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_RX_CHANNELS);
    localparam DMA_TX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_TX_CHANNELS) + 1;

    //META TO ITEM
    typedef uvm_app_core_top_agent::sequence_eth_item#(2**8, 16, MFB_ITEM_WIDTH)                                                   sequence_item_eth_rx;
    typedef uvm_app_core_top_agent::sequence_dma_item#(DMA_TX_CHANNELS, $clog2(DMA_PKT_MTU+1), DMA_HDR_META_WIDTH, MFB_ITEM_WIDTH) sequence_item_dma_rx;

    //TOP Sequencer
    uvm_app_core::sequencer#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                             ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH) m_sequencer;

    // ETHERNET I/O
    uvm_app_core_top_agent::agent#(sequence_item_eth_rx, MFB_ITEM_WIDTH, ETH_RX_HDR_WIDTH)                        m_eth_rx[ETH_STREAMS];
    uvm_logic_vector_array_mfb::env_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH)  m_eth_mfb_tx[ETH_STREAMS];
    // DMA I/O
    uvm_app_core_top_agent::agent#(sequence_item_dma_rx, MFB_ITEM_WIDTH, DMA_RX_MVB_WIDTH)                    m_dma_rx[DMA_STREAMS];
    uvm_logic_vector_mvb::env_tx#(REGIONS, DMA_TX_MVB_WIDTH)                                                  m_dma_mvb_tx[DMA_STREAMS];
    uvm_logic_vector_array_mfb::env_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)             m_dma_mfb_tx[DMA_STREAMS];
    //RESET
    uvm_reset::env#(4)         m_resets_gen;
    uvm_reset::agent           m_resets_mi;
    uvm_reset::env#(2)         m_resets_dma;
    uvm_reset::agent           m_resets_app;
    uvm_reset::env#(MEM_PORTS) m_resets_mem;
    //TSU
    uvm_logic_vector_mvb::env_rx #(1, 64) m_tsu;

    //CONFIGURATION INTERFACE
    uvm_mi::regmodel#(uvm_app_core::regmodel, MI_DATA_WIDTH, MI_ADDR_WIDTH) m_regmodel;

    //SCOREBOARD
    protected scoreboard #(ETH_STREAMS, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, MFB_ITEM_WIDTH) m_scoreboard;

    // ETH lower agetns. Convert ETH to ETH_MFB and ETH_MVB
    protected uvm_logic_vector_mvb::env_rx#(REGIONS, ETH_RX_HDR_WIDTH)                                        m_eth_mvb_rx[ETH_STREAMS];
    protected uvm_logic_vector_array_mfb::env_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)   m_eth_mfb_rx[ETH_STREAMS];
    // DMA lower agetns. Convert DMA to DMA_MFB and DMA_MVB
    protected uvm_logic_vector_mvb::env_rx#(REGIONS, DMA_RX_MVB_WIDTH)                                        m_dma_mvb_rx[DMA_STREAMS];
    protected uvm_logic_vector_array_mfb::env_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)   m_dma_mfb_rx[DMA_STREAMS];
    //MEMORY INTERFACE
    protected uvm_avmm::agent_master #(MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH) m_memory[MEM_PORTS];

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction


    function int unsigned used();
        int unsigned ret = 0;
        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            ret |= m_eth_rx[it].used();
        end

        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            ret |= m_dma_rx[it].used();
        end

        ret |= m_scoreboard.used();
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_mi::regmodel_config        m_mi_config;
        uvm_reset::env_config_item#(4) m_resets_gen_config;
        uvm_reset::config_item         m_resets_mi_config;
        uvm_reset::env_config_item#(2) m_resets_dma_config;
        uvm_reset::config_item         m_resets_app_config;
        uvm_reset::env_config_item#(MEM_PORTS) m_resets_mem_config;
        uvm_app_core_top_agent::config_item    m_eth_rx_config;
        uvm_app_core_top_agent::config_item    m_dma_rx_config;
        uvm_logic_vector_mvb::config_item      m_tsu_config;

        m_sequencer = uvm_app_core::sequencer#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                             ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH)::type_id::create("m_sequencer", this);

        ///////////////
        // ETH CONFIG
        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            uvm_logic_vector_mvb::config_item mvb_rx_config;
            uvm_logic_vector_array_mfb::config_item mfb_rx_config;
            uvm_logic_vector_array_mfb::config_item mfb_tx_config;
            string it_num;

            it_num.itoa(it);

            //RX ETH
            m_eth_rx_config = new();
            m_eth_rx_config.active         = UVM_ACTIVE;
            uvm_config_db#(uvm_app_core_top_agent::config_item)::set(this, {"m_eth_rx_", it_num}, "m_config", m_eth_rx_config);
            m_eth_rx[it] = uvm_app_core_top_agent::agent#(sequence_item_eth_rx, MFB_ITEM_WIDTH, ETH_RX_HDR_WIDTH)::type_id::create({"m_eth_rx_", it_num}, this);

            // RX MVB
            mvb_rx_config = new();
            mvb_rx_config.active         = UVM_ACTIVE;
            mvb_rx_config.interface_name = {"ETH_RX_MVB_", it_num};
            uvm_config_db#(uvm_logic_vector_mvb::config_item)::set(this, {"m_eth_mvb_rx_", it_num}, "m_config", mvb_rx_config);
            m_eth_mvb_rx[it] = uvm_logic_vector_mvb::env_rx#(REGIONS, ETH_RX_HDR_WIDTH)::type_id::create({"m_eth_mvb_rx_", it_num}, this);
            // RX MFB
            mfb_rx_config = new();
            mfb_rx_config.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_NONE;
            mfb_rx_config.active         = UVM_ACTIVE;
            mfb_rx_config.interface_name = {"ETH_RX_MFB_", it_num};
            uvm_config_db#(uvm_logic_vector_array_mfb::config_item)::set(this, {"m_eth_mfb_rx_", it_num}, "m_config", mfb_rx_config);
            m_eth_mfb_rx[it] = uvm_logic_vector_array_mfb::env_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create({"m_eth_mfb_rx_", it_num}, this); 
            // TX MFB
            mfb_tx_config = new();
            mfb_tx_config.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
            mfb_tx_config.active         = UVM_ACTIVE;
            mfb_tx_config.interface_name = {"ETH_TX_MFB_", it_num};
            uvm_config_db#(uvm_logic_vector_array_mfb::config_item)::set(this, {"m_eth_mfb_tx_", it_num}, "m_config", mfb_tx_config);
            m_eth_mfb_tx[it] = uvm_logic_vector_array_mfb::env_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH)::type_id::create({"m_eth_mfb_tx_", it_num}, this);
        end

        ///////////////
        // DMA CONFIG
        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            uvm_logic_vector_mvb::config_item   mvb_rx_config;
            uvm_logic_vector_array_mfb::config_item mfb_rx_config;
            uvm_logic_vector_mvb::config_item   mvb_tx_config;
            uvm_logic_vector_array_mfb::config_item mfb_tx_config;
            string it_num;
            it_num.itoa(it);
    
            //DMA
            m_dma_rx_config = new();
            m_dma_rx_config.active         = UVM_ACTIVE;
            uvm_config_db#(uvm_app_core_top_agent::config_item)::set(this, {"m_dma_rx_", it_num}, "m_config", m_dma_rx_config);
            m_dma_rx[it] = uvm_app_core_top_agent::agent#(sequence_item_dma_rx, MFB_ITEM_WIDTH, DMA_RX_MVB_WIDTH)::type_id::create({"m_dma_rx_", it_num}, this);

            // RX MVB
            mvb_rx_config = new();
            mvb_rx_config.active         = UVM_ACTIVE;
            mvb_rx_config.interface_name = {"DMA_RX_MVB_", it_num};
            uvm_config_db#(uvm_logic_vector_mvb::config_item)::set(this, {"m_dma_mvb_rx_", it_num}, "m_config", mvb_rx_config);
            m_dma_mvb_rx[it] = uvm_logic_vector_mvb::env_rx#(REGIONS, DMA_RX_MVB_WIDTH)::type_id::create({"m_dma_mvb_rx_", it_num}, this);
            // RX MFB
            mfb_rx_config = new();
            mfb_rx_config.active         = UVM_ACTIVE;
            mfb_rx_config.interface_name = {"DMA_RX_MFB_", it_num};
            uvm_config_db#(uvm_logic_vector_array_mfb::config_item)::set(this, {"m_dma_mfb_rx_", it_num}, "m_config", mfb_rx_config);
            m_dma_mfb_rx[it] = uvm_logic_vector_array_mfb::env_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create({"m_dma_mfb_rx_", it_num}, this);
            // TX MVB
            mvb_tx_config = new();
            mvb_tx_config.active         = UVM_ACTIVE;
            mvb_tx_config.interface_name = {"DMA_TX_MVB_", it_num};
            uvm_config_db#(uvm_logic_vector_mvb::config_item)::set(this, {"m_dma_mvb_tx_", it_num}, "m_config", mvb_tx_config);
            m_dma_mvb_tx[it] = uvm_logic_vector_mvb::env_tx#(REGIONS, DMA_TX_MVB_WIDTH)::type_id::create({"m_dma_mvb_tx_", it_num}, this);
            // TX MFB
            mfb_tx_config = new();
            mfb_tx_config.active         = UVM_ACTIVE;
            mfb_tx_config.interface_name = {"DMA_TX_MFB_", it_num};
            uvm_config_db#(uvm_logic_vector_array_mfb::config_item)::set(this, {"m_dma_mfb_tx_", it_num}, "m_config", mfb_tx_config);
            m_dma_mfb_tx[it] = uvm_logic_vector_array_mfb::env_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create({"m_dma_mfb_tx_", it_num}, this);
        end

        ///////////////
        // RESETS
        m_resets_gen_config = new();
        m_resets_gen_config.active[0]         = UVM_ACTIVE;
        m_resets_gen_config.interface_name[0] = "RESET_USER_X1";
        m_resets_gen_config.active[1]         = UVM_ACTIVE;
        m_resets_gen_config.interface_name[1] = "RESET_USER_X2";
        m_resets_gen_config.active[2]         = UVM_ACTIVE;
        m_resets_gen_config.interface_name[2] = "RESET_USER_X3";
        m_resets_gen_config.active[3]         = UVM_ACTIVE;
        m_resets_gen_config.interface_name[3] = "RESET_USER_X4";
        m_resets_gen_config.driver_delay      = 40ns;
        uvm_config_db#(uvm_reset::env_config_item#(4))::set(this, "m_reset_gen", "m_config", m_resets_gen_config);
        m_resets_gen = uvm_reset::env#(4)::type_id::create("m_reset_gen", this);

        m_resets_mi_config = new();
        m_resets_mi_config.active         = UVM_PASSIVE;
        m_resets_mi_config.interface_name = "RESET_MI";
        uvm_config_db#(uvm_reset::config_item)::set(this, "m_resets_mi", "m_config", m_resets_mi_config);
        m_resets_mi  = uvm_reset::agent::type_id::create("m_resets_mi", this);

        m_resets_dma_config = new();
        m_resets_dma_config.active[0]         = UVM_PASSIVE;
        m_resets_dma_config.interface_name[0] = "RESET_DMA_X1";
        m_resets_dma_config.active[1]         = UVM_PASSIVE;
        m_resets_dma_config.interface_name[1] = "RESET_DMA_X2";
        uvm_config_db#(uvm_reset::env_config_item#(2))::set(this, "m_resets_dma", "m_config", m_resets_dma_config);
        m_resets_dma = uvm_reset::env#(2)::type_id::create("m_resets_dma", this);

        m_resets_app_config = new();
        m_resets_app_config.active         = UVM_PASSIVE;
        m_resets_app_config.interface_name = "RESET_APP";
        uvm_config_db#(uvm_reset::config_item)::set(this, "m_resets_app", "m_config", m_resets_app_config);
        m_resets_app = uvm_reset::agent::type_id::create("m_resets_app", this);


        m_resets_mem_config = new();
        for(int unsigned it = 0; it < MEM_PORTS; it++) begin
            uvm_avmm::config_item mem_cfg;
            string it_num;
            it_num.itoa(it);

            m_resets_mem_config.active[it]         = UVM_ACTIVE;
            m_resets_mem_config.interface_name[it] = {"RESET_MEM_", it_num};

            mem_cfg = new();
            mem_cfg.active         = UVM_ACTIVE;
            mem_cfg.interface_name = {"MEM_", it_num};
            mem_cfg.generated_memory_file_type = uvm_avmm::config_item::RANDOM;
            uvm_config_db#(uvm_avmm::config_item)::set(this, {"m_memory_", it_num}, "m_config", mem_cfg);
            m_memory[it] = uvm_avmm::agent_master #(MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH)::type_id::create( {"m_memory_", it_num}, this);;
        end
        uvm_config_db#(uvm_reset::env_config_item#(MEM_PORTS))::set(this, "m_resets_mem", "m_config", m_resets_mem_config);
        m_resets_mem = uvm_reset::env#(MEM_PORTS)::type_id::create("m_resets_mem", this);


        //TSU
        m_tsu_config = new();
        m_tsu_config.active         = UVM_ACTIVE;
        m_tsu_config.interface_name = "TSU_INTERFACE";
        uvm_config_db#(uvm_logic_vector_mvb::config_item)::set(this, "m_tsu", "m_config", m_tsu_config);
        m_tsu = uvm_logic_vector_mvb::env_rx #(1, 64)::type_id::create("m_tsu", this);

        //CONFIGURATION INTERFACE
        m_mi_config = new();
        m_mi_config.addr_base            = 'h0;
        m_mi_config.agent.active         = UVM_ACTIVE;
        m_mi_config.agent.interface_name = "MI_INTERFACE";
        uvm_config_db#(uvm_mi::regmodel_config)::set(this, "m_regmodel", "m_config", m_mi_config);
        m_regmodel = uvm_mi::regmodel#(uvm_app_core::regmodel, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_regmodel", this);

        ///////////////
        // SCOREBOARD
        m_scoreboard = scoreboard #(ETH_STREAMS, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, MFB_ITEM_WIDTH)::type_id::create("m_scoreboard", this);
    endfunction

    function model#(ETH_STREAMS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, MFB_ITEM_WIDTH) model_get();
        return m_scoreboard.model_get();
    endfunction

    function void delay_max_set(time delay_max, time model_timeout = 1ms);
        m_scoreboard.timeout_set(delay_max, model_timeout);
    endfunction

    function void connect_phase(uvm_phase phase);
        m_resets_app.m_monitor.analysis_port.connect(m_scoreboard.analysis_imp_reset);

        //connect regmodel to model
        m_scoreboard.regmodel_set(m_regmodel.m_regmodel);


        m_sequencer.m_regmodel = m_regmodel.m_regmodel;
        m_sequencer.m_resets_gen = m_resets_gen.m_sequencer;
        m_sequencer.m_resets_mi  = m_resets_mi .m_sequencer;
        m_sequencer.m_resets_dma = m_resets_dma.m_sequencer;
        m_sequencer.m_resets_app = m_resets_app.m_sequencer;
        m_sequencer.m_resets_mem = m_resets_mem.m_sequencer;


        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);
            m_eth_rx[it].analysis_port.connect(m_scoreboard.eth_rx[it]);

            m_eth_mvb_rx[it].analysis_port.connect     (m_eth_rx[it].m_monitor.mvb.analysis_export);
            m_eth_mfb_rx[it].analysis_port_data.connect(m_eth_rx[it].m_monitor.mfb.analysis_export);
            m_eth_mfb_tx[it].analysis_port_data.connect(m_scoreboard.eth_mfb_tx[it]);
            m_eth_mfb_tx[it].analysis_port_meta.connect(m_scoreboard.eth_mvb_tx[it]);

            uvm_config_db#(uvm_common::fifo#(uvm_app_core_top_agent::sequence_item#(MFB_ITEM_WIDTH, ETH_RX_HDR_WIDTH)))::set(this, {"m_eth_mvb_rx_", it_num,".m_logic_vector_agent.m_sequencer"}      , "fifo", m_eth_rx[it].fifo_mvb);
            uvm_config_db#(uvm_common::fifo#(uvm_app_core_top_agent::sequence_item#(MFB_ITEM_WIDTH, ETH_RX_HDR_WIDTH)))::set(this, {"m_eth_mfb_rx_", it_num,".m_logic_vector_array_agent.m_sequencer"}, "fifo", m_eth_rx[it].fifo_mfb);

            m_resets_app.sync_connect(m_eth_rx[it].reset_sync);
            m_resets_app.sync_connect(m_eth_mvb_rx[it].reset_sync);
            m_resets_app.sync_connect(m_eth_mfb_rx[it].reset_sync);
            m_resets_app.sync_connect(m_eth_mfb_tx[it].reset_sync);

            m_sequencer.m_eth_rx[it] = m_eth_rx[it].m_sequencer;
            m_sequencer.m_eth_tx[it] = m_eth_mfb_tx[it].m_sequencer;
       end

        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);
            m_dma_rx[it].analysis_port.connect(m_scoreboard.dma_rx[it]);

            m_dma_mvb_rx[it].analysis_port.connect     (m_dma_rx[it].m_monitor.mvb.analysis_export);
            m_dma_mfb_rx[it].analysis_port_data.connect(m_dma_rx[it].m_monitor.mfb.analysis_export);
            m_dma_mvb_tx[it].analysis_port.connect(m_scoreboard.dma_mvb_tx[it]);
            m_dma_mfb_tx[it].analysis_port_data.connect(m_scoreboard.dma_mfb_tx[it]);

            uvm_config_db#(uvm_common::fifo#(uvm_app_core_top_agent::sequence_item#(MFB_ITEM_WIDTH, DMA_RX_MVB_WIDTH)))::set(this, {"m_dma_mvb_rx_", it_num,".m_logic_vector_agent.m_sequencer"}      , "fifo", m_dma_rx[it].fifo_mvb);
            uvm_config_db#(uvm_common::fifo#(uvm_app_core_top_agent::sequence_item#(MFB_ITEM_WIDTH, DMA_RX_MVB_WIDTH)))::set(this, {"m_dma_mfb_rx_", it_num,".m_logic_vector_array_agent.m_sequencer"}, "fifo", m_dma_rx[it].fifo_mfb);

            m_resets_app.sync_connect(m_dma_rx[it].reset_sync);
            m_resets_app.sync_connect(m_dma_mfb_rx[it].reset_sync);
            m_resets_app.sync_connect(m_dma_mvb_rx[it].reset_sync);
            m_resets_app.sync_connect(m_dma_mfb_tx[it].reset_sync);
            m_resets_app.sync_connect(m_dma_mvb_tx[it].reset_sync);

            m_sequencer.m_dma_rx    [it] = m_dma_rx    [it].m_sequencer;
            m_sequencer.m_dma_mvb_tx[it] = m_dma_mvb_tx[it].m_sequencer;
            m_sequencer.m_dma_mfb_tx[it] = m_dma_mfb_tx[it].m_sequencer;
        end

        for (int unsigned it = 0; it < MEM_PORTS; it++) begin
            m_sequencer.m_memory[it] = m_memory[it].m_sequencer;
        end
    endfunction

    task run_eth_meta(uvm_logic_vector::sequencer#(ETH_RX_HDR_WIDTH) sqr);
        uvm_app_core_top_agent::logic_vector_sequence#(MFB_ITEM_WIDTH, ETH_RX_HDR_WIDTH) meta_seq;

        meta_seq = uvm_app_core_top_agent::logic_vector_sequence#(MFB_ITEM_WIDTH, ETH_RX_HDR_WIDTH)::type_id::create("mvb_seq", this);

        forever begin
            //mvb_seq.set_starting_phase(phase);
            void'(meta_seq.randomize());
            meta_seq.start(sqr);
        end
    endtask

    task run_eth_packet(uvm_logic_vector_array::sequencer#(MFB_ITEM_WIDTH) sqr); 
        uvm_app_core_top_agent::logic_vector_array#(MFB_ITEM_WIDTH, ETH_RX_HDR_WIDTH) seq;
        seq = uvm_app_core_top_agent::logic_vector_array#(MFB_ITEM_WIDTH, ETH_RX_HDR_WIDTH)::type_id::create("seq", this);
        forever begin
            seq.randomize();
            seq.start(sqr);
        end
    endtask

    task run_dma_meta(uvm_logic_vector::sequencer#(DMA_RX_MVB_WIDTH) sqr);
        uvm_app_core_top_agent::logic_vector_sequence#(MFB_ITEM_WIDTH, DMA_RX_MVB_WIDTH) meta_seq;

        meta_seq = uvm_app_core_top_agent::logic_vector_sequence#(MFB_ITEM_WIDTH, DMA_RX_MVB_WIDTH)::type_id::create("mvb_seq", this);

        forever begin
            //mvb_seq.set_starting_phase(phase);
            void'(meta_seq.randomize());
            meta_seq.start(sqr);
        end
    endtask

    task run_dma_packet(uvm_logic_vector_array::sequencer#(MFB_ITEM_WIDTH) sqr); 
        uvm_app_core_top_agent::logic_vector_array#(MFB_ITEM_WIDTH, DMA_RX_MVB_WIDTH) seq;
        seq = uvm_app_core_top_agent::logic_vector_array#(MFB_ITEM_WIDTH, DMA_RX_MVB_WIDTH)::type_id::create("seq", this);
        forever begin
            seq.randomize();
            seq.start(sqr);
        end
    endtask



    task run_phase(uvm_phase phase);
        for(int unsigned it = 0; it < ETH_STREAMS; it++) begin
            fork
                automatic int index = it;
                run_eth_meta  (m_eth_mvb_rx[index].m_sequencer);
                run_eth_packet(m_eth_mfb_rx[index].m_sequencer.m_data);
            join_none;
        end

        // RUN DMA
        for(int unsigned it = 0; it < DMA_STREAMS; it++) begin
            fork
                automatic int index = it;
                run_dma_meta  (m_dma_mvb_rx[index].m_sequencer);
                run_dma_packet(m_dma_mfb_rx[index].m_sequencer.m_data);
            join_none;
        end
    endtask

endclass

