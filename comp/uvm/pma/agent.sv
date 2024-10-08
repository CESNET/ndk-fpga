/*
 * file       : agent.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: PMA agent
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef PMA_AGENT_SV
`define PMA_AGENT_SV

// This is PMA agent, which declares basic components.
class agent #(int unsigned DATA_WIDTH) extends uvm_agent;

    // Registration of agent to databaze.
    `uvm_component_param_utils(uvm_pma::agent #(DATA_WIDTH))

    // -----------------------
    // Variables.
    // -----------------------

    uvm_analysis_port #(sequence_item #(DATA_WIDTH)) analysis_port;

    // Agent base components sequencer, driver, monitor.
    sequencer #(DATA_WIDTH) m_sequencer;
    driver #(DATA_WIDTH) m_driver;
    monitor #(DATA_WIDTH) m_monitor;
    config_item m_config;

    // Constructor.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    // -----------------------
    // Functions.
    // -----------------------

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer #(DATA_WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver #(DATA_WIDTH)::type_id::create("m_driver", this);
        end
        m_monitor   = monitor #(DATA_WIDTH)::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);

        virtual pma_if #(DATA_WIDTH) vif;
        super.connect_phase(phase);

        if(!uvm_config_db #(virtual pma_if #(DATA_WIDTH))::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), "Cannot find 'pma_interface' inside uvm_config_db, probably not set!")
        end

        // Connect.
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
        // Driver.
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end
    endfunction

endclass

`endif
