/*
 * file       : agent.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: mi master and slave agent. Agent join all required class for driving interface into one class
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */


class agent_slave #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_agent;
    `uvm_component_param_utils(uvm_mi::agent_slave #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))


    uvm_analysis_port #(sequence_item_request #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)) analysis_port_rq;
    uvm_analysis_port #(sequence_item_response #(DATA_WIDTH))                         analysis_port_rs;

    sequencer_slave #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) m_sequencer;
    driver_slave    #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) m_driver;
    monitor           #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) m_monitor;
    config_item m_config;

    // Constructor.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end
        m_monitor   = monitor #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("m_monitor", this);
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer_slave #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver_slave    #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("m_driver", this);
        end

    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);
        virtual mi_if #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) vif;

        if(!uvm_config_db #(virtual mi_if #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), "Cannot find 'mi_interface' inside uvm_config_db, probably not set!")
        end

        // Connect.
        m_monitor.vif = vif;
        // Driver.
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end
       analysis_port_rq = m_monitor.analysis_port_rq;
       analysis_port_rs = m_monitor.analysis_port_rs;
    endfunction
endclass

// Slave agent is connected to slave DUT port. Master agent is connected to master DUT port.
class agent_master #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_agent;
    // Registration of agent to databaze.
    `uvm_component_param_utils(agent_master #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    //analysis ports
    uvm_analysis_port #(sequence_item_request #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)) analysis_port_rq;
    uvm_analysis_port #(sequence_item_response #(DATA_WIDTH))                         analysis_port_rs;

    // Agent base components sequencer, driver, monitor.
    sequencer_master #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) m_sequencer;
    driver_master    #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) m_driver;
    monitor            #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) m_monitor;
    config_item m_config;

    //reset sync
    uvm_reset::sync_cbs sync;

    // Constructor.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    // -----------------------
    // Functions.
    // -----------------------

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction


    function void build_phase(uvm_phase phase);
        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end
        m_monitor   = monitor #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("m_monitor", this);

        sync = new;
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer_master #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver_master    #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("m_driver", this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        virtual mi_if #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) vif;

        if(!uvm_config_db #(virtual mi_if #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), "Cannot find 'mi_interface' inside uvm_config_db, probably not set!")
        end

        // Connect.
        m_monitor.vif = vif;
        // Driver.
        if(get_is_active() == UVM_ACTIVE) begin
            sync.push_back(m_sequencer.sync);

            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end

       analysis_port_rq = m_monitor.analysis_port_rq;
       analysis_port_rs = m_monitor.analysis_port_rs;
    endfunction
endclass

