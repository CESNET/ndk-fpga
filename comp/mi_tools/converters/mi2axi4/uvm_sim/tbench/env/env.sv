//-- env.sv: Verification environment
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Environment for functional verification of encode.
// This environment containts two mii agents.
class env #(MI_DATA_WIDTH, MI_ADDRESS_WIDTH) extends uvm_env;

    `uvm_component_param_utils(uvm_mi2axi4lite::env #(MI_DATA_WIDTH, MI_ADDRESS_WIDTH));

    uvm_mi2axi4lite::virt_sequencer#(MI_DATA_WIDTH, MI_ADDRESS_WIDTH) vscr;

    uvm_reset::agent       m_reset;
    uvm_reset::config_item m_reset_config;

    uvm_mi::agent_slave #(MI_DATA_WIDTH, MI_ADDRESS_WIDTH) m_mi_agent;
    uvm_mi::config_item                                    m_mi_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        m_reset_config                = new;
        m_reset_config.active         = UVM_ACTIVE;
        m_reset_config.interface_name = "vif_reset";

        m_mi_config                = new();
        m_mi_config.active         = UVM_ACTIVE;
        m_mi_config.interface_name = "vif_mi";
        uvm_config_db#(uvm_mi::config_item)::set(this, "m_mi_agent", "m_config", m_mi_config);
        m_mi_agent = uvm_mi::agent_slave #(MI_DATA_WIDTH, MI_ADDRESS_WIDTH)::type_id::create("m_mi_agent", this);

        uvm_config_db#(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_reset_config);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        vscr   = uvm_mi2axi4lite::virt_sequencer#(MI_DATA_WIDTH, MI_ADDRESS_WIDTH)::type_id::create("vscr",this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        vscr.m_mi_sqr       = m_mi_agent.m_sequencer;
        vscr.m_reset_sqr    = m_reset.m_sequencer;
    endfunction
endclass
