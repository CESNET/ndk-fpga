/*
 * file       : env.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Test enviroment for intel mac seq adapter
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class env#(SEGMENTS, REGIONS, REGION_SIZE) extends uvm_env;
   `uvm_component_param_utils(uvm_mac_seg_rx::env#(SEGMENTS, REGIONS, REGION_SIZE))

    //sequnecer
    sequencer m_sequencer;

    uvm_reset::agent                                m_reset;
    uvm_logic_vector_array_intel_mac_seg::env_rx#(SEGMENTS) m_env_rx;
    uvm_logic_vector_array_mfb::env_tx      #(REGIONS, REGION_SIZE, 8, 8, 1) m_env_tx;
    //scoreboard
    scoreboard sc;

    function new (string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        //create configuration
        uvm_reset::config_item m_reset_cfg;
        uvm_logic_vector_array_intel_mac_seg::config_item m_env_rx_cfg;
        uvm_logic_vector_array_mfb::config_item           m_env_tx_cfg;

        //reset
        m_reset_cfg = new();
        m_reset_cfg.active = UVM_ACTIVE;
        m_reset_cfg.interface_name = "RESET_IF";
        uvm_config_db#(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_reset_cfg);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        m_env_rx_cfg = new();
        m_env_rx_cfg.active         = UVM_ACTIVE;
        m_env_rx_cfg.interface_name = "RX_MAC_SEQ_IF";
        uvm_config_db#(uvm_logic_vector_array_intel_mac_seg::config_item)::set(this, "m_env_rx", "m_config", m_env_rx_cfg);
        m_env_rx = uvm_logic_vector_array_intel_mac_seg::env_rx#(SEGMENTS)::type_id::create("m_env_rx", this);

        m_env_tx_cfg = new();
        m_env_tx_cfg.active         = UVM_ACTIVE;
        m_env_tx_cfg.interface_name = "TX_MAC_SEQ_IF";
        m_env_tx_cfg.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_EOF;
        uvm_config_db#(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_tx", "m_config", m_env_tx_cfg);
        m_env_tx = uvm_logic_vector_array_mfb::env_tx  #(REGIONS, REGION_SIZE, 8, 8, 1)::type_id::create("m_env_tx", this);

        sc       = scoreboard::type_id::create("sc", this);

        m_sequencer = sequencer::type_id::create("m_sequencer", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        m_env_rx.analysis_port_packet.connect(sc.analysis_export_rx_packet);
        m_env_rx.analysis_port_error.connect(sc.analysis_export_rx_error);

        m_env_tx.analysis_port_data.connect(sc.analysis_export_tx_packet);
        m_env_tx.analysis_port_meta.connect(sc.analysis_export_tx_error);

        m_sequencer.rx_packet  = m_env_rx.m_sequencer.m_packet;
        m_sequencer.rx_error   = m_env_rx.m_sequencer.m_error;
        m_sequencer.reset      = m_reset.m_sequencer;

        m_reset.sync_connect(m_env_rx.reset_sync);
    endfunction

    task run_tx_seq();
        //TX have to allways ready
        uvm_mfb::sequence_full_speed_tx #(REGIONS, REGION_SIZE, 8, 8, 1) tx_seq;
        tx_seq = uvm_mfb::sequence_full_speed_tx #(REGIONS, REGION_SIZE, 8, 8, 1)::type_id::create("tx_seq");

        forever begin
            tx_seq.randomize();
            tx_seq.start(m_env_tx.m_sequencer);
        end
    endtask

    task run_phase(uvm_phase phase);
        fork
            run_tx_seq();
        join_none
    endtask
endclass

