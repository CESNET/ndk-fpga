//-- env.sv: Verification environment
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// This enviroment is used for verification of splitter simple
class env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH,  META_WIDTH, SPLITTER_OUTPUTS, META_BEHAV) extends uvm_env;
    `uvm_component_param_utils(uvm_splitter_simple::env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, SPLITTER_OUTPUTS, META_BEHAV));

    uvm_reset::agent                                                           m_reset;
    uvm_logic_vector_array_mfb::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, $clog2(SPLITTER_OUTPUTS) +META_WIDTH) m_env_rx;
    uvm_logic_vector_array_mfb::env_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)                           m_env_tx[SPLITTER_OUTPUTS];

    scoreboard #(ITEM_WIDTH, META_WIDTH, SPLITTER_OUTPUTS) sc;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_reset::config_item          m_config_reset;
        uvm_logic_vector_array_mfb::config_item m_config_rx;
        uvm_logic_vector_array_mfb::config_item m_config_tx[SPLITTER_OUTPUTS];

        m_config_reset = new();
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";
        uvm_config_db#(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset  = uvm_reset::agent::type_id::create("m_reset", this);


        m_config_rx = new;
        m_config_rx.active = UVM_ACTIVE;
        m_config_rx.interface_name = "vif_rx";
        m_config_rx.meta_behav = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_rx", "m_config", m_config_rx);
        m_env_rx = uvm_logic_vector_array_mfb::env_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, $clog2(SPLITTER_OUTPUTS) +META_WIDTH)::type_id::create("m_env_rx", this);

        for(int i = 0; i < SPLITTER_OUTPUTS; i++) begin
            string i_string;
            i_string.itoa(i);

            m_config_tx[i] = new;
            m_config_tx[i].active = UVM_ACTIVE;
            m_config_tx[i].interface_name = {"vif_tx_", i_string};
            m_config_tx[i].meta_behav = uvm_logic_vector_array_mfb::config_item::META_SOF;
            uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, {"m_env_tx_", i_string}, "m_config", m_config_tx[i]);
            m_env_tx[i]    = uvm_logic_vector_array_mfb::env_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create({"m_env_tx_", i_string}, this);
        end

        sc  = scoreboard #(ITEM_WIDTH, META_WIDTH, SPLITTER_OUTPUTS)::type_id::create("sc", this);

    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        m_reset.analysis_port.connect(sc.analysis_imp_reset);

        m_env_rx.analysis_port_data.connect(sc.input_data);
        m_env_rx.analysis_port_meta.connect(sc.input_meta);
        m_reset.sync_connect(m_env_rx.reset_sync);

        for (int i = 0; i < SPLITTER_OUTPUTS; i++) begin
            m_env_tx[i].analysis_port_data.connect(sc.out_data[i]);
            m_env_tx[i].analysis_port_meta.connect(sc.out_meta[i]);
            m_reset.sync_connect(m_env_tx[i].reset_sync);
        end
    endfunction

endclass
