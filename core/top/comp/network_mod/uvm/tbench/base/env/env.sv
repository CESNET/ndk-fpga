//-- env.sv: Verification environment
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class env #(
    string ETH_CORE_ARCH,
    int unsigned ETH_PORTS        ,

    int unsigned ETH_PORT_SPEED[ETH_PORTS-1:0],
    int unsigned ETH_PORT_CHAN[ETH_PORTS-1:0]    ,

    int unsigned ETH_TX_HDR_WIDTH,
    int unsigned ETH_RX_HDR_WIDTH,

    int unsigned REGIONS          ,
    int unsigned REGION_SIZE      ,
    int unsigned BLOCK_SIZE       ,
    int unsigned ITEM_WIDTH       ,

    int unsigned MI_DATA_WIDTH    ,
    int unsigned MI_ADDR_WIDTH


) extends uvm_env;
    `uvm_component_param_utils(uvm_network_mod_env::env#(
        ETH_CORE_ARCH,
        ETH_PORTS,
        ETH_PORT_SPEED,
        ETH_PORT_CHAN,
        ETH_TX_HDR_WIDTH,
        ETH_RX_HDR_WIDTH,
        REGIONS,
        REGION_SIZE,
        BLOCK_SIZE,
        ITEM_WIDTH,
        MI_DATA_WIDTH,
        MI_ADDR_WIDTH
    ));

    sequencer#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH) m_sequencer;

    //RESETS
    protected uvm_reset::agent m_usr_rst;
    protected uvm_reset::agent m_eth_rst[ETH_PORTS];
    protected uvm_reset::agent m_mi_rst;
    protected uvm_reset::agent m_mi_phy_rst;
    protected uvm_reset::agent m_mi_pmd_rst;
    protected uvm_reset::agent m_tsu_rst;

    //USR
    protected uvm_logic_vector_array_mfb::env_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, ETH_TX_HDR_WIDTH) m_usr_rx[ETH_PORTS];
    protected uvm_logic_vector_array_mfb::env_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)                m_usr_tx_data[ETH_PORTS];
    protected uvm_logic_vector_mvb::env_tx      #(REGIONS, ETH_RX_HDR_WIDTH)                                      m_usr_tx_hdr[ETH_PORTS];

    //MI
    //protected uvm_mi::agent_slave #(MI_DATA_WIDTH, MI_ADDR_WIDTH) m_mi;
    protected uvm_mi::agent_slave #(MI_DATA_WIDTH, MI_ADDR_WIDTH) m_mi_pmd;
    protected uvm_mi::agent_slave #(MI_DATA_WIDTH, MI_ADDR_WIDTH) m_mi_phy;

    // TSU
    protected uvm_logic_vector_mvb::env_rx      #(1, 64) m_tsu;

    // SCOREBOARD
    protected scoreboard #(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, REGIONS, ITEM_WIDTH, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH) m_scoreboard;
    protected uvm_mi::regmodel#(uvm_network_mod_env::regmodel #(ETH_PORTS, ETH_PORT_CHAN), MI_DATA_WIDTH, MI_ADDR_WIDTH) m_regmodel;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        return m_scoreboard.used();
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_reset::config_item cfg_rst;
        uvm_logic_vector_mvb::config_item       cfg_tsu;
        //uvm_mi::config_item     cfg_mi;
        uvm_mi::regmodel_config  cfg_mi;
        uvm_mi::config_item      cfg_mi_phy;
        uvm_mi::config_item      cfg_mi_pmd;

        //RESETS
        super.build_phase(phase);
        cfg_rst = new();
        cfg_rst.active = UVM_ACTIVE;
        cfg_rst.interface_name = "vif_rst_usr";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_usr_rst", "m_config", cfg_rst);
        m_usr_rst = uvm_reset::agent::type_id::create("m_usr_rst", this);

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            cfg_rst = new();
            cfg_rst.active = UVM_ACTIVE;
            cfg_rst.interface_name = $sformatf("vif_rst_eth_%0d", it);
            uvm_config_db #(uvm_reset::config_item)::set(this, $sformatf("eth_rst_%0d", it), "m_config", cfg_rst);
            m_eth_rst[it] = uvm_reset::agent::type_id::create($sformatf("eth_rst_%0d", it), this);
        end

        cfg_rst = new();
        cfg_rst.active = UVM_ACTIVE;
        cfg_rst.interface_name = "vif_rst_mi";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_mi_rst", "m_config", cfg_rst);
        m_mi_rst = uvm_reset::agent::type_id::create("m_mi_rst", this);

        cfg_rst = new();
        cfg_rst.active = UVM_ACTIVE;
        cfg_rst.interface_name = "vif_rst_mi_phy";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_mi_phy_rst", "m_config", cfg_rst);
        m_mi_phy_rst = uvm_reset::agent::type_id::create("m_mi_phy_rst", this);

        cfg_rst = new();
        cfg_rst.active = UVM_ACTIVE;
        cfg_rst.interface_name = "vif_rst_mi_pmd";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_mi_pmd_rst", "m_config", cfg_rst);
        m_mi_pmd_rst = uvm_reset::agent::type_id::create("m_mi_pmd_rst", this);

        cfg_rst = new();
        cfg_rst.active = UVM_ACTIVE;
        cfg_rst.interface_name = "vif_rst_tsu";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_tsu_rst", "m_config", cfg_rst);
        m_tsu_rst = uvm_reset::agent::type_id::create("m_tsu_rst", this);

        // usr
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            uvm_logic_vector_array_mfb::config_item cfg_rx;
            uvm_logic_vector_array_mfb::config_item cfg_tx_data;
            uvm_logic_vector_mvb::config_item       cfg_tx_hdr;

            cfg_rx = new();
            cfg_rx.active = UVM_ACTIVE;
            cfg_rx.interface_name = $sformatf("vif_usr_rx_%0d", it);
            cfg_rx.meta_behav = uvm_logic_vector_array_mfb::config_item::META_SOF;
            uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, $sformatf("m_usr_rx_%0d", it), "m_config", cfg_rx);
            m_usr_rx[it]      = uvm_logic_vector_array_mfb::env_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, ETH_TX_HDR_WIDTH)::type_id::create($sformatf("m_usr_rx_%0d", it), this);

            cfg_tx_data = new();
            cfg_tx_data.active = UVM_ACTIVE;
            cfg_tx_data.interface_name = $sformatf("vif_usr_tx_data_%0d", it);
            cfg_tx_data.meta_behav = uvm_logic_vector_array_mfb::config_item::META_NONE;
            uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, $sformatf("m_usr_tx_data_%0d", it), "m_config", cfg_tx_data);
            m_usr_tx_data[it] = uvm_logic_vector_array_mfb::env_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)::type_id::create($sformatf("m_usr_tx_data_%0d", it), this);

            cfg_tx_hdr = new();
            cfg_tx_hdr.active = UVM_ACTIVE;
            cfg_tx_hdr.interface_name = $sformatf("vif_usr_tx_hdr_%0d", it);
            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, $sformatf("m_usr_tx_hdr_%0d", it), "m_config", cfg_tx_hdr);
            m_usr_tx_hdr[it]  = uvm_logic_vector_mvb::env_tx#(REGIONS, ETH_RX_HDR_WIDTH)::type_id::create($sformatf("m_usr_tx_hdr_%0d", it), this);
        end

        cfg_mi  = new();
        cfg_mi.addr_base            = 'h0;
        cfg_mi.agent.active         = UVM_ACTIVE;
        cfg_mi.agent.interface_name = "vif_mi";
        uvm_config_db#(uvm_mi::regmodel_config)::set(this, "m_regmodel", "m_config", cfg_mi);
        m_regmodel = uvm_mi::regmodel#(uvm_network_mod_env::regmodel #(ETH_PORTS, ETH_PORT_CHAN), MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_regmodel", this);;

        cfg_mi_phy  = new();
        cfg_mi_phy.active         = UVM_ACTIVE;
        cfg_mi_phy.interface_name = "vif_mi_phy";
        uvm_config_db #(uvm_mi::config_item)::set(this, "m_mi_phy", "m_config", cfg_mi_phy);
        m_mi_phy = uvm_mi::agent_slave #(MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_mi_phy", this);

        cfg_mi_pmd  = new();
        cfg_mi_pmd.active         = UVM_ACTIVE;
        cfg_mi_pmd.interface_name = "vif_mi_pmd";
        uvm_config_db #(uvm_mi::config_item)::set(this, "m_mi_pmd", "m_config", cfg_mi_pmd);
        m_mi_pmd = uvm_mi::agent_slave #(MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_mi_pmd", this);

        cfg_tsu = new();
        cfg_tsu.active = UVM_ACTIVE;
        cfg_tsu.interface_name = "vif_tsu";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_tsu", "m_config", cfg_tsu);
        m_tsu  = uvm_logic_vector_mvb::env_rx#(1, 64)::type_id::create("m_tsu", this);

        m_scoreboard = scoreboard#(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, REGIONS, ITEM_WIDTH, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH)::type_id::create("m_scoreboard", this);
        m_sequencer  = sequencer#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_sequencer", this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            m_usr_rst.sync_connect(m_usr_rx     [it].reset_sync);
            m_usr_rst.sync_connect(m_usr_tx_data[it].reset_sync);
            m_usr_rst.sync_connect(m_usr_tx_hdr [it].reset_sync);
        end
        m_tsu_rst.sync_connect(m_tsu.reset_sync);

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            m_usr_rx[it].analysis_port_data.connect(m_scoreboard.usr_rx_data[it]);
            m_usr_rx[it].analysis_port_meta.connect(m_scoreboard.usr_rx_hdr[it]);

            m_usr_tx_data[it].analysis_port_data.connect(m_scoreboard.usr_tx_data[it]);
            m_usr_tx_hdr[it].analysis_port.connect(m_scoreboard.usr_tx_hdr[it]);
        end

        m_sequencer.usr_rst = m_usr_rst.m_sequencer;
        m_sequencer.mi_rst = m_mi_rst.m_sequencer;
        m_sequencer.mi_phy_rst = m_mi_phy_rst.m_sequencer;
        m_sequencer.mi_pmd_rst = m_mi_pmd_rst.m_sequencer;
        m_sequencer.tsu_rst    = m_tsu_rst.m_sequencer;
        m_sequencer.set_regmodel(m_regmodel.m_regmodel);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            m_sequencer.port[it].eth_rst     = m_eth_rst[it].m_sequencer;
            m_sequencer.port[it].usr_rx_data = m_usr_rx[it].m_sequencer.m_data;
            m_sequencer.port[it].usr_rx_meta = m_usr_rx[it].m_sequencer.m_meta;
            m_sequencer.port[it].usr_tx_data = m_usr_tx_data[it].m_sequencer;
            m_sequencer.port[it].usr_tx_hdr  = m_usr_tx_hdr[it].m_sequencer;
        end
    endfunction
endclass

