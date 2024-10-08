// speed.sv: Test for full speed on input
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_seq_full_speed #(
    int unsigned USR_MFB_REGIONS,
    int unsigned USR_MFB_REGION_SIZE,
    int unsigned USR_MFB_BLOCK_SIZE,
    int unsigned USR_MFB_ITEM_WIDTH,
    int unsigned CHANNELS,
    int unsigned HDR_META_WIDTH,
    int unsigned PKT_SIZE_MAX
) extends virt_seq #(
    USR_MFB_REGIONS,
    USR_MFB_REGION_SIZE,
    USR_MFB_BLOCK_SIZE,
    USR_MFB_ITEM_WIDTH,
    CHANNELS,
    HDR_META_WIDTH,
    PKT_SIZE_MAX
);

    `uvm_object_param_utils(test::virt_seq_full_speed #(
        USR_MFB_REGIONS,
        USR_MFB_REGION_SIZE,
        USR_MFB_BLOCK_SIZE,
        USR_MFB_ITEM_WIDTH,
        CHANNELS,
        HDR_META_WIDTH,
        PKT_SIZE_MAX)
    )

    `uvm_declare_p_sequencer(uvm_tx_dma_calypte::sequencer #(
        USR_MFB_REGIONS,
        USR_MFB_REGION_SIZE,
        USR_MFB_BLOCK_SIZE,
        USR_MFB_ITEM_WIDTH,
        CHANNELS,
        HDR_META_WIDTH,
        PKT_SIZE_MAX)
    )

    localparam USR_META_WIDTH = HDR_META_WIDTH + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);

    function new (string name = "virt_seq_full_speed");
        super.new(name);
    endfunction

    virtual function void init();
        super.init();
        m_usr_mfb_seq = uvm_mfb::sequence_full_speed_tx #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, USR_META_WIDTH)::type_id::create("m_usr_mfb_seq");
    endfunction
endclass

class tx_mfb_seq_lib_speed #(
    int unsigned MFB_REGIONS,
    int unsigned MFB_REGION_SIZE,
    int unsigned MFB_BLOCK_SIZE,
    int unsigned MFB_ITEM_WIDTH,
    int unsigned MFB_META_WIDTH
) extends uvm_logic_vector_array_mfb::sequence_lib_pcie_rx #(
    MFB_REGIONS,
    MFB_REGION_SIZE,
    MFB_BLOCK_SIZE,
    MFB_ITEM_WIDTH,
    MFB_META_WIDTH
);

  `uvm_object_param_utils(    tx_mfb_seq_lib_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))
  `uvm_sequence_library_utils(tx_mfb_seq_lib_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))

    function new(string name = "tx_mfb_seq_lib_speed");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(uvm_logic_vector_array_mfb::config_sequence param_cfg = null);
        if (param_cfg == null) begin
            this.cfg = new();
        end else begin
            this.cfg = param_cfg;
        end

        this.add_sequence(uvm_logic_vector_array_mfb::sequence_full_speed_pcie_rx #(MFB_REGIONS, MFB_REGION_SIZE, BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::get_type());
    endfunction
endclass

class speed extends base;
    typedef uvm_component_registry#(test::speed, "test::speed") type_id;

    uvm_tx_dma_calypte::env #(
        DEVICE,
        MI_WIDTH,

        USR_MFB_REGIONS,
        USR_MFB_REGION_SIZE,
        USR_MFB_BLOCK_SIZE,
        USR_MFB_ITEM_WIDTH,

        PCIE_CQ_MFB_REGIONS,
        PCIE_CQ_MFB_REGION_SIZE,
        PCIE_CQ_MFB_BLOCK_SIZE,
        PCIE_CQ_MFB_ITEM_WIDTH,

        CHANNELS,
        HDR_META_WIDTH,
        DATA_POINTER_WIDTH,
        PKT_SIZE_MAX,
        PCIE_LEN_MAX
    ) m_env;

    bit            timeout;
    uvm_reg_data_t pkt_cnt          [CHANNELS];
    uvm_reg_data_t byte_cnt         [CHANNELS];
    uvm_reg_data_t discard_pkt_cnt  [CHANNELS];
    uvm_reg_data_t discard_byte_cnt [CHANNELS];
    uvm_status_e   status_r;

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    static function type_id get_type();
        return type_id::get();
    endfunction

    function string get_type_name();
        return get_type().get_type_name();
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array_mfb::sequence_lib_pcie_rx #(
            PCIE_CQ_MFB_REGIONS,
            PCIE_CQ_MFB_REGION_SIZE,
            PCIE_CQ_MFB_BLOCK_SIZE,
            PCIE_CQ_MFB_ITEM_WIDTH,
            sv_pcie_meta_pack::PCIE_CQ_META_WIDTH
        )::type_id::set_inst_override(tx_mfb_seq_lib_speed #(
            PCIE_CQ_MFB_REGIONS,
            PCIE_CQ_MFB_REGION_SIZE,
            PCIE_CQ_MFB_BLOCK_SIZE,
            PCIE_CQ_MFB_ITEM_WIDTH,
            sv_pcie_meta_pack::PCIE_CQ_META_WIDTH
        )::get_type(), {this.get_full_name(), ".m_env.m_env_rx.*"});

        m_env = uvm_tx_dma_calypte::env #(
            DEVICE,
            MI_WIDTH,

            USR_MFB_REGIONS,
            USR_MFB_REGION_SIZE,
            USR_MFB_BLOCK_SIZE,
            USR_MFB_ITEM_WIDTH,

            PCIE_CQ_MFB_REGIONS,
            PCIE_CQ_MFB_REGION_SIZE,
            PCIE_CQ_MFB_BLOCK_SIZE,
            PCIE_CQ_MFB_ITEM_WIDTH,

            CHANNELS,
            HDR_META_WIDTH,
            DATA_POINTER_WIDTH,
            PKT_SIZE_MAX,
            PCIE_LEN_MAX
        )::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    virtual task run_phase(uvm_phase phase);
        time time_start;
        virt_seq_full_speed #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, CHANNELS, HDR_META_WIDTH, PKT_SIZE_MAX) m_virt_seq;

        m_virt_seq = virt_seq_full_speed #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, CHANNELS, HDR_META_WIDTH, PKT_SIZE_MAX)::type_id::create("m_virt_seq");

        phase.raise_objection(this);

        m_virt_seq.init();
        m_virt_seq.randomize();
        m_virt_seq.start(m_env.m_sequencer);

        time_start = $time();
        while((time_start + 500us) > $time() && m_env.m_scoreboard.used()) begin
            #(600ns);
        end

        for (int unsigned chan = 0; chan < CHANNELS; chan++) begin

            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].sent_packets_reg.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].sent_packets_reg.read(status_r, pkt_cnt[chan]);
            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].sent_bytes_reg.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].sent_bytes_reg.read(status_r, byte_cnt[chan]);

            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].discarded_packets_reg.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].discarded_packets_reg.read(status_r, discard_pkt_cnt[chan]);
            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].discarded_bytes_reg.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].discarded_bytes_reg.read(status_r, discard_byte_cnt[chan]);

            m_env.m_scoreboard.byte_cnt[chan]         = byte_cnt[chan];
            m_env.m_scoreboard.pkt_cnt[chan]          = pkt_cnt[chan];
            m_env.m_scoreboard.discard_byte_cnt[chan] = discard_byte_cnt[chan];
            m_env.m_scoreboard.discard_pkt_cnt[chan]  = discard_pkt_cnt[chan];
        end

        phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass
