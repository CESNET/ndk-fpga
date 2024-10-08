//-- agent.sv: packet agent
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

class agent #(type TR_TYPE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_agent;
    // registration of component tools
    `uvm_component_param_utils(uvm_app_core_top_agent::agent#(TR_TYPE, ITEM_WIDTH, META_WIDTH))

    // -----------------------
    // Variables.
    // -----------------------
    uvm_reset::sync_cbs       reset_sync;

    uvm_analysis_port#(TR_TYPE)        analysis_port;
    sequencer#(ITEM_WIDTH, META_WIDTH) m_sequencer;

    uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH)) fifo_mvb;
    uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH)) fifo_mfb;

    protected driver#(ITEM_WIDTH, META_WIDTH)           m_driver;
    /*protected*/ monitor#(TR_TYPE, ITEM_WIDTH, META_WIDTH) m_monitor;
    protected config_item                               m_config;

    // Contructor, where analysis port is created.
    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        reset_sync  = new();
    endfunction: new


    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_driver.used() != 0);
        return ret;
    endfunction

    // -----------------------
    // Functions.
    // -----------------------
    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Get configurg file from
        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        if (get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer#(ITEM_WIDTH, META_WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver#(ITEM_WIDTH, META_WIDTH)::type_id::create   ("m_driver",    this);
            m_driver.m_config = m_config;

            fifo_mvb = uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH))::type_id::create("fifo_mvb", this);
            fifo_mfb = uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH))::type_id::create("fifo_mfb", this);
        end
        m_monitor   = monitor#(TR_TYPE, ITEM_WIDTH, META_WIDTH)::type_id::create("m_monitor",   this);
        analysis_port = m_monitor.analysis_port;
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        if (get_is_active() == UVM_ACTIVE) begin
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
            reset_sync.push_back(m_driver.reset_sync);
            reset_sync.push_back(m_sequencer.reset_sync);

            uvm_config_db#(uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH)))::set(this, "m_driver", "fifo_mvb", fifo_mvb);
            uvm_config_db#(uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH)))::set(this, "m_driver", "fifo_mfb", fifo_mfb);
        end
    endfunction
endclass

