/*
 * file       : env.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: verification eviroment for application core
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class env #(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_env;
    `uvm_component_param_utils(app_core::env#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    // ETHERNET I/O
    uvm_mvb::agent_rx#(REGIONS, ETH_RX_HDR_WIDTH)                                                            m_eth_mvb_rx[ETH_STREAMS];
    uvm_byte_array_mfb::env_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, 0)                m_eth_mfb_rx[ETH_STREAMS];
    uvm_byte_array_mfb::env_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, ETH_TX_HDR_WIDTH) m_eth_mfb_tx[ETH_STREAMS];
    // DMA I/O
    localparam DMA_RX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_TX_CHANNELS);
    localparam DMA_TX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_RX_CHANNELS) + 1;
    uvm_mvb::agent_rx#(REGIONS, DMA_RX_MVB_WIDTH)                                               m_dma_mvb_rx[DMA_STREAMS];
    uvm_byte_array_mfb::env_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, 0)   m_dma_mfb_rx[DMA_STREAMS];
    uvm_mvb::agent_tx#(REGIONS, DMA_TX_MVB_WIDTH)                               m_dma_mvb_tx[DMA_STREAMS];
    uvm_byte_array_mfb::env_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, 0)   m_dma_mfb_tx[DMA_STREAMS];
    //RESET
    uvm_reset::env#(4)         m_resets_gen;
    uvm_reset::agent           m_resets_mi;
    uvm_reset::env#(2)         m_resets_dma;
    uvm_reset::agent           m_resets_app;
    uvm_reset::env#(MEM_PORTS) m_resets_mem;

    //CONFIGURATION INTERFACE
    uvm_mi::regmodel#(app_core::regmodel #(ETH_STREAMS, ETH_CHANNELS, DMA_RX_CHANNELS), MI_DATA_WIDTH, MI_ADDR_WIDTH) m_regmodel;

    //SCOREBOARD
    scoreboard #(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, MI_DATA_WIDTH, MI_ADDR_WIDTH) m_scoreboard;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_mi::regmodel_config        m_mi_config;
        uvm_reset::env_config_item#(4) m_resets_gen_config;
        uvm_reset::config_item         m_resets_mi_config;
        uvm_reset::env_config_item#(2) m_resets_dma_config;
        uvm_reset::config_item         m_resets_app_config;
        uvm_reset::env_config_item#(MEM_PORTS) m_resets_mem_config;
        ///////////////
        // ETH CONFIG
        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            uvm_mvb::config_item                mvb_rx_config;
            uvm_byte_array_mfb::config_item mfb_rx_config;
            uvm_byte_array_mfb::config_item mfb_tx_config;
            string it_num;

            it_num.itoa(it);

            // TOP ENV
            //m_eth_agent[it] = top_agent::agent::type_it::create({"m_eth_agent_", it_num}, this);

            // RX MVB
            mvb_rx_config = new();
            mvb_rx_config.active         = UVM_ACTIVE;
            mvb_rx_config.interface_name = {"ETH_RX_MVB_", it_num};
            uvm_config_db#(uvm_mvb::config_item)::set(this, {"m_eth_mvb_rx_", it_num}, "m_config", mvb_rx_config);
            m_eth_mvb_rx[it] = uvm_mvb::agent_rx#(REGIONS, ETH_RX_HDR_WIDTH)::type_id::create({"m_eth_mvb_rx_", it_num}, this);
            // RX MFB
            mfb_rx_config = new();
            mfb_rx_config.active         = UVM_ACTIVE;
            mfb_rx_config.interface_name = {"ETH_RX_MFB_", it_num};
            uvm_config_db#(uvm_byte_array_mfb::config_item)::set(this, {"m_eth_mfb_rx_", it_num}, "m_config", mfb_rx_config);
            m_eth_mfb_rx[it] = uvm_byte_array_mfb::env_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, 0)::type_id::create({"m_eth_mfb_rx_", it_num}, this); 
            // TX MFB
            mfb_tx_config = new();
            mfb_tx_config.meta_behav     = 1;
            mfb_tx_config.active         = UVM_ACTIVE;
            mfb_tx_config.interface_name = {"ETH_TX_MFB_", it_num};
            uvm_config_db#(uvm_byte_array_mfb::config_item)::set(this, {"m_eth_mfb_tx_", it_num}, "m_config", mfb_tx_config);
            m_eth_mfb_tx[it] = uvm_byte_array_mfb::env_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, ETH_TX_HDR_WIDTH)::type_id::create({"m_eth_mfb_tx_", it_num}, this);
        end

        ///////////////
        // DMA CONFIG
        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            uvm_mvb::config_item                mvb_rx_config;
            uvm_byte_array_mfb::config_item mfb_rx_config;
            uvm_mvb::config_item                mvb_tx_config;
            uvm_byte_array_mfb::config_item mfb_tx_config;
            string it_num;
            it_num.itoa(it);

            // RX MVB
            mvb_rx_config = new();
            mvb_rx_config.active         = UVM_ACTIVE;
            mvb_rx_config.interface_name = {"DMA_RX_MVB_", it_num};
            uvm_config_db#(uvm_mvb::config_item)::set(this, {"m_dma_mvb_rx_", it_num}, "m_config", mvb_rx_config);
            m_dma_mvb_rx[it] = uvm_mvb::agent_rx#(REGIONS, DMA_RX_MVB_WIDTH)::type_id::create({"m_dma_mvb_rx_", it_num}, this);
            // RX MFB
            mfb_rx_config = new();
            mfb_rx_config.active         = UVM_ACTIVE;
            mfb_rx_config.interface_name = {"DMA_RX_MFB_", it_num};
            uvm_config_db#(uvm_byte_array_mfb::config_item)::set(this, {"m_dma_mfb_rx_", it_num}, "m_config", mfb_rx_config);
            m_dma_mfb_rx[it] = uvm_byte_array_mfb::env_rx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, 0)::type_id::create({"m_dma_mfb_rx_", it_num}, this);
            // TX MVB
            mvb_tx_config = new();
            mvb_tx_config.active         = UVM_ACTIVE;
            mvb_tx_config.interface_name = {"DMA_TX_MVB_", it_num};
            uvm_config_db#(uvm_mvb::config_item)::set(this, {"m_dma_mvb_tx_", it_num}, "m_config", mvb_tx_config);
            m_dma_mvb_tx[it] = uvm_mvb::agent_tx#(REGIONS, DMA_TX_MVB_WIDTH)::type_id::create({"m_dma_mvb_tx_", it_num}, this);
            // TX MFB
            mfb_tx_config = new();
            mfb_tx_config.active         = UVM_ACTIVE;
            mfb_tx_config.interface_name = {"DMA_TX_MFB_", it_num};
            uvm_config_db#(uvm_byte_array_mfb::config_item)::set(this, {"m_dma_mfb_tx_", it_num}, "m_config", mfb_tx_config);
            m_dma_mfb_tx[it] = uvm_byte_array_mfb::env_tx#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, 0)::type_id::create({"m_dma_mfb_tx_", it_num}, this);
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
            string it_num;
            it_num.itoa(it);

            m_resets_mem_config.active[it]         = UVM_ACTIVE;
            m_resets_mem_config.interface_name[it] = {"RESET_MEM_", it_num};
        end
        uvm_config_db#(uvm_reset::env_config_item#(MEM_PORTS))::set(this, "m_resets_mem", "m_config", m_resets_mem_config);
        m_resets_mem = uvm_reset::env#(MEM_PORTS)::type_id::create("m_resets_mem", this);


        //CONFIGURATION INTERFACE
        m_mi_config = new();
        m_mi_config.addr_base            = 'h0;
        m_mi_config.agent.active         = UVM_ACTIVE;
        m_mi_config.agent.interface_name = "MI_INTERFACE";
        uvm_config_db#(uvm_mi::regmodel_config)::set(this, "m_regmodel", "m_config", m_mi_config);
        m_regmodel = uvm_mi::regmodel#(app_core::regmodel #(ETH_STREAMS, ETH_CHANNELS, DMA_RX_CHANNELS), MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_regmodel", this);

        ///////////////
        // SCOREBOARD
        m_scoreboard = scoreboard #(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_scoreboard", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        m_resets_app.m_monitor.analysis_port.connect(m_scoreboard.m_model.analysis_imp_reset);
        m_resets_app.m_monitor.analysis_port.connect(m_scoreboard.analysis_imp_reset);
        //m_resets_app.sync_connect(m_scoreboard.reset_sync);

        //connect regmodel to model
        m_scoreboard.m_model.regmodel_set(m_regmodel.m_regmodel);

        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);
            m_eth_mvb_rx[it].analysis_port.connect(m_scoreboard.eth_mvb_rx[it]);
            m_eth_mfb_rx[it].analysis_port_data.connect(m_scoreboard.eth_mfb_rx[it]);
            m_eth_mfb_tx[it].analysis_port_data.connect(m_scoreboard.eth_mfb_tx[it]);
            m_eth_mfb_tx[it].analysis_port_meta.connect(m_scoreboard.eth_mvb_tx[it]);

            m_resets_app.sync_connect(m_eth_mfb_rx[it].reset_sync);
            m_resets_app.sync_connect(m_eth_mvb_rx[it].reset_sync);
            m_resets_app.sync_connect(m_eth_mfb_tx[it].reset_sync);
       end

        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);
            m_dma_mvb_rx[it].analysis_port.connect(m_scoreboard.dma_mvb_rx[it]);
            m_dma_mfb_rx[it].analysis_port_data.connect(m_scoreboard.dma_mfb_rx[it]);
            m_dma_mvb_tx[it].analysis_port.connect(m_scoreboard.dma_mvb_tx[it]);
            m_dma_mfb_tx[it].analysis_port_data.connect(m_scoreboard.dma_mfb_tx[it]);

            m_resets_app.sync_connect(m_dma_mfb_rx[it].reset_sync);
            m_resets_app.sync_connect(m_dma_mvb_rx[it].reset_sync);
            m_resets_app.sync_connect(m_dma_mfb_tx[it].reset_sync);
            m_resets_app.sync_connect(m_dma_mvb_tx[it].reset_sync);
        end
    endfunction
endclass

