/*
 * file       : env.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Environment for Block Lock
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

class env #(SH_CNT_MAX, SH_INVALID_CNT_MAX, SLIP_WAIT_TIME) extends uvm_env;

    `uvm_component_param_utils(uvm_blklock::env #(SH_CNT_MAX, SH_INVALID_CNT_MAX, SLIP_WAIT_TIME));

    uvm_mvb::agent_rx #(1, 2) agent_rx;
    uvm_mvb::agent_tx #(1, 2) agent_tx;

    uvm_reset::agent    reset_agent;

    scoreboard#(SH_CNT_MAX, SH_INVALID_CNT_MAX, SLIP_WAIT_TIME) m_scoreboard;
    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        uvm_mvb::config_item cfg_rx = new;
        uvm_mvb::config_item cfg_tx = new;

        uvm_reset::config_item rst_cfg = new;

        cfg_rx.active = UVM_ACTIVE;
        cfg_tx.active = UVM_PASSIVE;

        rst_cfg.active = UVM_ACTIVE;

        cfg_rx.interface_name = "vif_rx";
        cfg_tx.interface_name = "vif_tx";

        rst_cfg.interface_name = "rst_vif";

        uvm_config_db #(uvm_mvb::config_item)::set(this, "agent_rx", "m_config", cfg_rx);
        uvm_config_db #(uvm_mvb::config_item)::set(this, "agent_tx", "m_config", cfg_tx);
        uvm_config_db #(uvm_reset::config_item)::set(this, "reset_agent", "m_config", rst_cfg);

        agent_rx    = uvm_mvb::agent_rx #(1, 2)::type_id::create("agent_rx", this);
        agent_tx    = uvm_mvb::agent_tx #(1, 2)::type_id::create("agent_tx", this);
        reset_agent = uvm_reset::agent::type_id::create("reset_agent", this);

        m_scoreboard = scoreboard#(SH_CNT_MAX, SH_INVALID_CNT_MAX, SLIP_WAIT_TIME)::type_id::create("m_scoreboard", this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        agent_rx.analysis_port.connect(m_scoreboard.analysis_imp_mvb_rx);
        agent_tx.analysis_port.connect(m_scoreboard.analysis_imp_mvb_tx);

        reset_agent.analysis_port.connect(m_scoreboard.analysis_imp_reset);

    endfunction
endclass
