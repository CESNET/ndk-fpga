//-- env.sv: Verification environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author: Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Environment for functional verification of encode.
// This environment containts two mii agents.
class env #(
    INPUT_WIDTH,
    BOX_WIDTH,
    BOX_CNT,
    READ_PRIOR,
    CLEAR_BY_READ,
    CLEAR_BY_RST,
    DEVICE,
    REQ_WIDTH,
    RESP_WIDTH,
    ADDR_WIDTH
) extends uvm_env;

    `uvm_component_param_utils(uvm_histogramer::env #(
        INPUT_WIDTH,
        BOX_WIDTH,
        BOX_CNT,
        READ_PRIOR,
        CLEAR_BY_READ,
        CLEAR_BY_RST,
        DEVICE,
        REQ_WIDTH,
        RESP_WIDTH,
        ADDR_WIDTH
    ));

    uvm_logic_vector_mvb::env_rx #(1, REQ_WIDTH) req_env;
    uvm_logic_vector_mvb::config_item cfg_req;
    uvm_logic_vector_mvb::env_tx #(1, RESP_WIDTH) resp_env;
    uvm_logic_vector_mvb::config_item cfg_resp;

    uvm_reset::agent        m_reset;
    uvm_reset::config_item  m_config_reset;

    uvm_histogramer::virt_sequencer #(
        INPUT_WIDTH,
        BOX_WIDTH,
        BOX_CNT,
        READ_PRIOR,
        CLEAR_BY_READ,
        CLEAR_BY_RST,
        DEVICE,
        REQ_WIDTH,
        RESP_WIDTH,
        ADDR_WIDTH
    ) vscr;

    scoreboard #(
        INPUT_WIDTH,
        BOX_WIDTH,
        BOX_CNT,
        READ_PRIOR,
        CLEAR_BY_READ,
        CLEAR_BY_RST,
        DEVICE,
        REQ_WIDTH,
        RESP_WIDTH,
        ADDR_WIDTH
    ) m_scoreboard;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        cfg_req                     = new;
        cfg_resp                    = new;

        cfg_req.active              = UVM_ACTIVE;
        cfg_resp.active             = UVM_PASSIVE;

        cfg_req.interface_name      = "vif_req";
        cfg_resp.interface_name     = "vif_resp";

        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";

        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        cfg_req.coverage = 1;
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "req_env",    "m_config", cfg_req);

        cfg_resp.coverage = 1;
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "resp_env",   "m_config", cfg_resp);

        req_env    = uvm_logic_vector_mvb::env_rx #(1, REQ_WIDTH) ::type_id::create("req_env",  this);
        resp_env   = uvm_logic_vector_mvb::env_tx #(1, RESP_WIDTH)::type_id::create("resp_env", this);

        vscr          = uvm_histogramer::virt_sequencer#(
            INPUT_WIDTH,
            BOX_WIDTH,
            BOX_CNT,
            READ_PRIOR,
            CLEAR_BY_READ,
            CLEAR_BY_RST,
            DEVICE,
            REQ_WIDTH,
            RESP_WIDTH,
            ADDR_WIDTH
        )::type_id::create("vscr", this);
        m_scoreboard  = scoreboard#(
            INPUT_WIDTH,
            BOX_WIDTH,
            BOX_CNT,
            READ_PRIOR,
            CLEAR_BY_READ,
            CLEAR_BY_RST,
            DEVICE,
            REQ_WIDTH,
            RESP_WIDTH,
            ADDR_WIDTH
        )::type_id::create("m_scoreboard", this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        req_env.analysis_port.connect(m_scoreboard.in_data);
        resp_env.analysis_port.connect(m_scoreboard.out_data);

        m_reset.sync_connect(req_env.reset_sync);
        m_reset.sync_connect(resp_env.reset_sync);

        vscr.m_reset    = m_reset.m_sequencer;
        vscr.req_sqr    = req_env.m_sequencer;
    endfunction
endclass
