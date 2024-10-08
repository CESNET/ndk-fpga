/*
 * file       : enviroment with reg model.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: mi package. configuration of designs
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class reg2bus #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_env;
    `uvm_component_param_utils(uvm_mi::reg2bus#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    uvm_reg_predictor #(reg2bus_class)                      predictor;
    reg2bus_adapter#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)    adapter;
    reg2bus_monitor#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)    monitor;

    reg2bus_frontdoor #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) frontdoor;

    function new(string name = "regmodel", uvm_component parent);
        super.new(name, parent);
    endfunction

   function void build_phase(uvm_phase phase);
        predictor = new("predictor", this);
        adapter   = reg2bus_adapter#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("reg2mi", ,this.get_full_name());
        frontdoor = reg2bus_frontdoor #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("frontdoor", this);
        monitor   = reg2bus_monitor#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("monitor", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        predictor.adapter = adapter;
        monitor.analysis_port.connect(predictor.bus_in);
    endfunction
endclass


class regmodel_config;

    config_item    agent;
    uvm_reg_addr_t addr_base;

    function new();
        agent = new();
    endfunction
endclass


class regmodel #(type REG_TYPE, int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_env;
    `uvm_component_param_utils(uvm_mi::regmodel#(REG_TYPE, DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    regmodel_config                                   m_config;
    agent_slave #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) m_agent;
    reg2bus#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)      reg2mi;
    REG_TYPE                                          m_regmodel;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        config_item  m_agent_config;

        if(!uvm_config_db #(regmodel_config)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "\n\tUnable to get configuration object")
        end

        if (m_config.agent.active == UVM_PASSIVE) begin
            `uvm_fatal(this.get_full_name(), "\n\tThis component doesnt support PASSIVE version. It is implemented in future if it will be needed")
        end

        uvm_config_db#(uvm_mi::config_item)::set(this, "m_agent", "m_config", m_config.agent);


        m_agent     = agent_slave #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("m_agent", this);
        reg2mi      = reg2bus#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("reg2mi", this);
        m_regmodel  = REG_TYPE::type_id::create("m_regmodel", this);
        m_regmodel.build(m_config.addr_base, DATA_WIDTH);
    endfunction

    function void connect_phase(uvm_phase phase);
        // REGISTER MODEL
        if (m_regmodel.get_parent() == null) begin

            m_regmodel.set_frontdoor(reg2mi.frontdoor);
            m_regmodel.default_map.set_sequencer(m_agent.m_sequencer, reg2mi.adapter);
            m_regmodel.default_map.set_auto_predict(0);

            reg2mi.frontdoor.configure(m_regmodel.default_map);
            reg2mi.predictor.map     = m_regmodel.default_map;
        end

        m_agent.m_monitor.analysis_port_rq.connect(reg2mi.monitor.analysis_imp_rq);
        m_agent.m_monitor.analysis_port_rs.connect(reg2mi.monitor.analysis_imp_rs);
    endfunction
endclass


