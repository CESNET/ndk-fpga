/*
 * file       : env.sv
 * description: verry simple and not correct way how to generate asynchronous reset synchronously
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: RESET packages
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/



class env #(int unsigned RESETS) extends uvm_env;
    `uvm_component_param_utils(uvm_reset::env#(RESETS));

    //high level
    env_config_item#(RESETS) m_config;
    sequencer  m_sequencer;
    env_driver m_driver;

    //low lewel
    agent m_agent[RESETS];

    function new (string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if (!uvm_config_db#(env_config_item#(RESETS))::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_type_name(), "Unable to get configuration object");
        end

        m_sequencer = sequencer::type_id::create("m_sequencer", this);
        m_driver    = env_driver::type_id::create("m_driver", this);
        m_driver.delay = m_config.driver_delay;

        for (int unsigned it = 0; it < RESETS; it++) begin
            string num;
            config_item low_config;

            num.itoa(it);

            low_config = new();
            low_config.active = m_config.active[it];
            low_config.interface_name = m_config.interface_name[it];

            uvm_config_db #(config_item)::set(this, {"m_agent_", num}, "m_config", low_config);
            m_agent[it] = agent::type_id::create({"m_agent_", num}, this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
    endfunction

    task run_seq(int unsigned index);
        if (m_config.active[index] == UVM_ACTIVE) begin
            low_sequence seq;
            seq = low_sequence::type_id::create("seq");
            seq.randomize();
            seq.driver = m_driver;

            seq.start(m_agent[index].m_sequencer);
        end
    endtask

    task run_phase(uvm_phase phase);
        //run sequences
        begin
            for (int unsigned it = 0; it < RESETS; it++) begin
                fork
                    automatic int index = it;
                    run_seq(index);
                join_none
            end
            //wait for all sequences
            wait fork;
        end
    endtask
endclass


