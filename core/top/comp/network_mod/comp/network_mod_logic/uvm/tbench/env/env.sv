// env.sv: Verification environment
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause 


class env_base #(USER_REGIONS, USER_REGION_SIZE, CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, USER_MVB_WIDTH, ETH_CHANNELS, RX_MAC_LITE_REGIONS) extends uvm_env;
    `uvm_component_param_utils(net_mod_logic_env::env_base #(USER_REGIONS, USER_REGION_SIZE, CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, USER_MVB_WIDTH, ETH_CHANNELS, RX_MAC_LITE_REGIONS));

    // TX path
    uvm_logic_vector_array_mfb::env_rx #(USER_REGIONS, USER_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_user_rx_mfb_env;
    uvm_logic_vector_array_mfb::env_tx #(CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0         ) m_core_tx_mfb_env[ETH_CHANNELS];

    // RX path
    uvm_logic_vector_array_mfb::env_rx #(CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0         ) m_core_rx_mfb_env[ETH_CHANNELS]; // no META
    uvm_logic_vector_array_mfb::env_tx #(USER_REGIONS, USER_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0         ) m_user_tx_mfb_env; // no META
    uvm_logic_vector_mvb::env_tx       #(USER_REGIONS, USER_MVB_WIDTH                                      ) m_user_tx_mvb_env;

    // MVB discard
    uvm_logic_vector_mvb::env_tx #(RX_MAC_LITE_REGIONS, 1) m_mvb_discard_env[ETH_CHANNELS];

    // MI
    uvm_mi::regmodel #(net_mod_logic_env::mac_reg#(ETH_CHANNELS), 32, 32) m_regmodel; // MI_DATA_WIDTH, MI_ADDR_WIDTH
    uvm_mi::regmodel_config                                               m_mi_config;

    scoreboard #(ETH_CHANNELS, USER_REGIONS, ITEM_WIDTH, META_WIDTH, USER_MVB_WIDTH, RX_MAC_LITE_REGIONS) sc;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array_mfb::config_item m_user_rx_mfb_config;
        uvm_logic_vector_array_mfb::config_item m_core_tx_mfb_config[ETH_CHANNELS];
        uvm_logic_vector_array_mfb::config_item m_user_tx_mfb_config;
        uvm_logic_vector_array_mfb::config_item m_core_rx_mfb_config[ETH_CHANNELS];
        uvm_logic_vector_mvb::config_item                m_user_tx_mvb_config;

        // TX path ------------------------------------------------------------------------------------------------------------------------------------------------------
        // USER (RX) environment
        m_user_rx_mfb_config = new;
        m_user_rx_mfb_config.active = UVM_ACTIVE;
        m_user_rx_mfb_config.interface_name = "vif_user_rx_mfb";
        m_user_rx_mfb_config.meta_behav = uvm_logic_vector_array_mfb::config_item::META_SOF;

        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_user_rx_mfb_env_", "m_config", m_user_rx_mfb_config);
        m_user_rx_mfb_env = uvm_logic_vector_array_mfb::env_rx#(USER_REGIONS, USER_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("m_user_rx_mfb_env_", this);

        // CORE (TX) environment
        for(int i = 0; i < ETH_CHANNELS; i++) begin
            string i_string;
            i_string.itoa(i);

            m_core_tx_mfb_config[i] = new;
            m_core_tx_mfb_config[i].active = UVM_ACTIVE;
            m_core_tx_mfb_config[i].interface_name = {"vif_core_tx_mfb_", i_string};
            m_core_tx_mfb_config[i].meta_behav = uvm_logic_vector_array_mfb::config_item::META_SOF;

            uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, {"m_core_tx_mfb_env_", i_string}, "m_config", m_core_tx_mfb_config[i]);
            m_core_tx_mfb_env[i] = uvm_logic_vector_array_mfb::env_tx#(CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)::type_id::create({"m_core_tx_mfb_env_", i_string}, this);
        end

        // RX path ------------------------------------------------------------------------------------------------------------------------------------------------------
        // CORE (RX) environment
        for(int i = 0; i < ETH_CHANNELS; i++) begin
            string i_string;
            i_string.itoa(i);

            m_core_rx_mfb_config[i] = new;
            m_core_rx_mfb_config[i].active = UVM_ACTIVE;
            m_core_rx_mfb_config[i].interface_name = {"vif_core_rx_mfb_", i_string};
            m_core_rx_mfb_config[i].meta_behav = uvm_logic_vector_array_mfb::config_item::META_SOF; // meta not actually needed

            uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, {"m_core_rx_mfb_env_", i_string}, "m_config", m_core_rx_mfb_config[i]);
            m_core_rx_mfb_env[i] = uvm_logic_vector_array_mfb::env_rx#(CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)::type_id::create({"m_core_rx_mfb_env_", i_string}, this);
        end

        // USER (TX) environment
        m_user_tx_mfb_config = new;
        m_user_tx_mfb_config.active = UVM_ACTIVE;
        m_user_tx_mfb_config.interface_name = "vif_user_tx_mfb";
        m_user_tx_mfb_config.meta_behav = uvm_logic_vector_array_mfb::config_item::META_SOF;

        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_user_tx_mfb_env_", "m_config", m_user_tx_mfb_config);
        m_user_tx_mfb_env = uvm_logic_vector_array_mfb::env_tx#(USER_REGIONS, USER_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)::type_id::create("m_user_tx_mfb_env_", this);

        m_user_tx_mvb_config = new;
        m_user_tx_mvb_config.active = UVM_ACTIVE;
        m_user_tx_mvb_config.interface_name = "vif_user_tx_mvb";

        uvm_config_db#(uvm_logic_vector_mvb::config_item)::set(this, "m_user_tx_mvb_env_", "m_config", m_user_tx_mvb_config);
        m_user_tx_mvb_env = uvm_logic_vector_mvb::env_tx#(USER_REGIONS, USER_MVB_WIDTH)::type_id::create("m_user_tx_mvb_env_", this);

        // MVB discard --------------------------------------------------------------------------------------------------------------------------------------------------
        for(int i = 0; i < ETH_CHANNELS; i++) begin
            string i_string;
            uvm_logic_vector_mvb::config_item m_mvb_discard_config;
            i_string.itoa(i);

            m_mvb_discard_config = new;
            m_mvb_discard_config.active = UVM_PASSIVE;
            m_mvb_discard_config.interface_name = {"vif_mvb_discard_", i_string};

            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, {"m_mvb_discard_env_", i_string}, "m_config", m_mvb_discard_config);
            m_mvb_discard_env[i] = uvm_logic_vector_mvb::env_tx#(RX_MAC_LITE_REGIONS, 1)::type_id::create({"m_mvb_discard_env_", i_string}, this);
        end

        // -------------------------------------------------------------------------------------------------------------------------------------------------------------

        // Scoreboard
        sc = scoreboard #(ETH_CHANNELS, USER_REGIONS, ITEM_WIDTH, META_WIDTH, USER_MVB_WIDTH, RX_MAC_LITE_REGIONS)::type_id::create("sc", this);

        // Configuration interface
        m_mi_config = new;
        m_mi_config.addr_base            = 'h0;
        m_mi_config.agent.active         = UVM_ACTIVE;
        m_mi_config.agent.interface_name = "MI_INTERFACE";
        uvm_config_db #(uvm_mi::regmodel_config)::set(this, "m_regmodel", "m_config", m_mi_config);
        m_regmodel = uvm_mi::regmodel #(net_mod_logic_env::mac_reg#(ETH_CHANNELS), 32, 32)::type_id::create("m_regmodel", this);

    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        // TX path
        m_user_rx_mfb_env.analysis_port_data.connect(sc.tx_input_data);
        m_user_rx_mfb_env.analysis_port_meta.connect(sc.tx_input_meta);
        for (int i = 0; i < ETH_CHANNELS; i++) begin
            m_core_tx_mfb_env[i].analysis_port_data.connect(sc.tx_out[i]);
        end

        // RX path
        for (int i = 0; i < ETH_CHANNELS; i++) begin
            m_core_rx_mfb_env[i].analysis_port_data.connect(sc.rx_input_data[i]);
        end
        m_user_tx_mfb_env.analysis_port_data.connect(sc.rx_out_data);
        m_user_tx_mvb_env.analysis_port.connect(sc.rx_out_hdr);

        // MVB discard
        for (int i = 0; i < ETH_CHANNELS; i++) begin
            m_mvb_discard_env[i].analysis_port.connect(sc.mvb_discard[i]);
        end

    endfunction
endclass
