//-- env.sv: Verification environment
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Environment for functional verification of encode.
// This environment containts two mii agents.
class env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE,
            MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_mtc::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH,
                                              DEVICE, ENDPOINT_TYPE, MI_DATA_WIDTH, MI_ADDR_WIDTH));

    localparam CC_MFB_META_WIDTH = sv_pcie_meta_pack::PCIE_CC_META_WIDTH;
    localparam CQ_MFB_META_WIDTH = sv_pcie_meta_pack::PCIE_CQ_META_WIDTH;

    sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) m_sequencer;

    uvm_reset::agent                                                                                                          m_reset;
    uvm_pcie_cq::env                   #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE) m_env_cq;
    uvm_logic_vector_array_mfb::env_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, CC_MFB_META_WIDTH)     m_env_cc;
    uvm_mi::agent_master #(MI_DATA_WIDTH, MI_ADDR_WIDTH)                                                                      m_mi_agent;
    uvm_pcie_hdr::sync_tag tag_sync;
    uvm_mtc::tr_planner #(MI_DATA_WIDTH, MI_ADDR_WIDTH) tr_plan;
    monitor #(MI_DATA_WIDTH, MI_ADDR_WIDTH) m_monitor;

    scoreboard #(MFB_ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) sc;
    uvm_mi::config_item                     m_mi_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_reset::config_item                  m_config_reset;
        uvm_pcie_cq::config_item                m_config_cq;
        uvm_logic_vector_array_mfb::config_item m_config_cc;

        m_config_reset                   = new;
        m_config_reset.active            = UVM_ACTIVE;
        m_config_reset.interface_name    = "vif_reset";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset    = uvm_reset::agent::type_id::create("m_reset", this);

        m_config_cq                      = new;
        m_config_cq.active               = UVM_ACTIVE;
        m_config_cq.interface_name       = "vif_cq";
        uvm_config_db #(uvm_pcie_cq::config_item)::set(this, "m_env_cq", "m_config", m_config_cq);
        m_env_cq   = uvm_pcie_cq::env#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE)::type_id::create("m_env_cq", this);

        m_config_cc                      = new;
        m_config_cc.active               = UVM_ACTIVE;
        m_config_cc.interface_name       = "vif_cc";
        m_config_cc.meta_behav           = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_cc", "m_config", m_config_cc);
        m_env_cc   = uvm_logic_vector_array_mfb::env_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, CC_MFB_META_WIDTH)::type_id::create("m_env_cc", this);

        m_mi_config                = new();
        m_mi_config.active         = UVM_ACTIVE;
        m_mi_config.interface_name = "vif_mi";
        uvm_config_db#(uvm_mi::config_item)::set(this, "m_mi_agent", "m_config", m_mi_config);
        m_mi_agent = uvm_mi::agent_master #(MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_mi_agent", this);

        //change Select devices
        set_type_override_by_type(uvm_mtc::model #(MFB_ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH)::get_type(), uvm_mtc::model_base #(MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE, MI_DATA_WIDTH, MI_ADDR_WIDTH)::get_type());
        sc          = scoreboard #(MFB_ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("sc", this);
        m_sequencer = sequencer  #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_sequencer", this);

        tag_sync  = uvm_pcie_hdr::sync_tag::type_id::create("tag_sync", this);
        m_monitor = monitor #(MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_monitor", this);
        tr_plan   = uvm_mtc::tr_planner #(MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("tr_plan", this);

    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        m_sequencer.m_reset  = m_reset.m_sequencer;
        m_sequencer.m_packet = m_env_cq.m_pcie_hdr_agent.m_sequencer;
        m_sequencer.m_pcie   = m_env_cc.m_sequencer;
        m_sequencer.m_mi_sqr = m_mi_agent.m_sequencer;

        m_env_cq.m_env_rx.analysis_port_data.connect(sc.analysis_export_cq_data);
        m_env_cq.m_env_rx.analysis_port_meta.connect(sc.analysis_export_cq_meta);
        m_env_cq.m_env_rx.analysis_port_data.connect(sc.analysis_export_cq_data);
        m_env_cq.m_env_rx.analysis_port_meta.connect(sc.analysis_export_cq_meta);
        m_mi_agent.analysis_port_rs.connect(sc.analysis_export_cc_mi);
        sc.m_mi_cmp_rq.mi_analysis_port_out.connect(m_monitor.analysis_export);

        m_reset.sync_connect(m_env_cq.reset_sync);
        m_reset.sync_connect(m_env_cc.reset_sync);

        m_env_cc.analysis_port_data.connect(sc.analysis_export_cc_data);
        m_env_cc.analysis_port_meta.connect(sc.analysis_export_cc_meta);
        m_mi_agent.analysis_port_rq.connect(sc.mi_scrb.analysis_export);

        m_monitor.analysis_port.connect(tr_plan.analysis_imp);

    endfunction

    virtual task run_phase(uvm_phase phase);
        m_env_cq.m_driver.tag_sync = tag_sync;
        sc.m_mi_cmp_rs.tag_sync = tag_sync;
        if (m_mi_config.active == UVM_ACTIVE) begin
            uvm_mtc::mi_cc_sequence #(MI_DATA_WIDTH, MI_ADDR_WIDTH) mi_seq;

            mi_seq         = uvm_mtc::mi_cc_sequence #(MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("mi_seq", this);
            mi_seq.tr_plan = tr_plan;
            mi_seq.randomize();

            fork
                mi_seq.start(m_mi_agent.m_sequencer);
            join_none

        end
    endtask

endclass
