// env.sv
// Copyright (C) 2022-2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env #(
    string       DEVICE,
    int unsigned MFB_REGIONS,
    int unsigned MFB_REGION_SIZE,
    int unsigned MFB_BLOCK_SIZE,
    int unsigned MFB_ITEM_WIDTH,
    int unsigned CHANNELS,
    int unsigned DATA_POINTER_WIDTH,
    int unsigned PCIE_LEN_MAX
) extends uvm_env;

    `uvm_component_param_utils(uvm_tx_dma_calypte_cq::env #(DEVICE, MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, CHANNELS, DATA_POINTER_WIDTH, PCIE_LEN_MAX));

    sequencer                                                                    m_sequencer [CHANNELS];
    driver #(DEVICE, MFB_ITEM_WIDTH, CHANNELS, DATA_POINTER_WIDTH, PCIE_LEN_MAX) m_driver    [CHANNELS];

    uvm_reset::sync_cbs                                                                                                                       m_reset_sync;
    uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CQ_META_WIDTH) m_rx_mfb_env;

    local driver_sync #(MFB_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CQ_META_WIDTH) m_data_export;
    local uvm_tx_dma_calypte_regs::regmodel_top #(CHANNELS)                    m_regmodel_top;
    local config_item                                                          m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void regmodel_set(uvm_tx_dma_calypte_regs::regmodel_top #(CHANNELS) regmodel);
        this.m_regmodel_top = regmodel;

        for (int unsigned it = 0; it < CHANNELS; it++) begin
            m_sequencer[it].regmodel_set(m_regmodel_top.m_regmodel_channel[it]);
            m_driver[it]   .regmodel_set(m_regmodel_top.m_regmodel_channel[it]);
        end
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array_mfb::config_item m_rx_mfb_env_cfg;

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        // LOW level agent
        m_rx_mfb_env_cfg                = new;
        m_rx_mfb_env_cfg.active         = m_config.active;
        m_rx_mfb_env_cfg.seq_type       = "PCIE";
        m_rx_mfb_env_cfg.interface_name = m_config.interface_name;
        m_rx_mfb_env_cfg.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;

        m_rx_mfb_env_cfg.seq_cfg = new();
        m_rx_mfb_env_cfg.seq_cfg.straddling = 1;

        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_rx_mfb_env", "m_config", m_rx_mfb_env_cfg);
        m_rx_mfb_env  = uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)::type_id::create("m_rx_mfb_env", this);

        for (int unsigned chan = 0; chan < CHANNELS; chan++) begin
            string i_string = $sformatf("%0d", chan);

            if (m_config.active == UVM_ACTIVE) begin
                m_sequencer[chan]        = sequencer::type_id::create({"m_sequencer_", i_string}, this);
                m_driver[chan]           = driver #(DEVICE, MFB_ITEM_WIDTH, CHANNELS, DATA_POINTER_WIDTH, PCIE_LEN_MAX)::type_id::create({"m_driver_", i_string}, this);
                m_driver[chan].m_channel = chan;
            end else begin
                m_sequencer[chan] = null;
                m_driver[chan]    = null;
            end
        end

        m_reset_sync  = new();
        m_data_export = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin

            for (int unsigned chan = 0; chan < CHANNELS; chan++) begin

                m_driver[chan].seq_item_port.connect(m_sequencer[chan].seq_item_export);
                m_driver[chan].m_data_export = m_data_export;
                m_reset_sync.push_back(m_sequencer[chan].m_reset_sync);
                m_reset_sync.push_back(m_driver[chan].m_reset_terminate);
            end
        end
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            base_send_sequence #(uvm_logic_vector::sequence_item #(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)) meta_seq;
            base_send_sequence #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))                  data_seq;

            meta_seq = base_send_sequence #(uvm_logic_vector::sequence_item #(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH))::type_id::create("meta_seq", this);
            data_seq = base_send_sequence #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))                 ::type_id::create("data_seq", this);

            meta_seq.m_tr_export = m_data_export.pcie_meta;
            data_seq.m_tr_export = m_data_export.pcie_data;

            meta_seq.randomize();
            data_seq.randomize();

            fork
                meta_seq.start(m_rx_mfb_env.m_sequencer.m_meta);
                data_seq.start(m_rx_mfb_env.m_sequencer.m_data);
            join
        end
    endtask
endclass


