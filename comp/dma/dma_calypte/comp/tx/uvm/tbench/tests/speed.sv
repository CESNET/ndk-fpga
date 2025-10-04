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
    int unsigned PKT_SIZE_MAX,
    int unsigned DATA_POINTER_WIDTH,
    int unsigned PCIE_RQ_REGIONS,
    int unsigned PCIE_RQ_REGION_SIZE,
    int unsigned PCIE_RQ_BLOCK_SIZE,
    int unsigned PCIE_RQ_ITEM_WIDTH
) extends virt_seq #(
    USR_MFB_REGIONS,
    USR_MFB_REGION_SIZE,
    USR_MFB_BLOCK_SIZE,
    USR_MFB_ITEM_WIDTH,
    CHANNELS,
    HDR_META_WIDTH,
    PKT_SIZE_MAX,
    DATA_POINTER_WIDTH,
    PCIE_RQ_REGIONS,
    PCIE_RQ_REGION_SIZE,
    PCIE_RQ_BLOCK_SIZE,
    PCIE_RQ_ITEM_WIDTH
);

    `uvm_object_param_utils(test::virt_seq_full_speed #(
        USR_MFB_REGIONS,
        USR_MFB_REGION_SIZE,
        USR_MFB_BLOCK_SIZE,
        USR_MFB_ITEM_WIDTH,
        CHANNELS,
        HDR_META_WIDTH,
        PKT_SIZE_MAX,
        DATA_POINTER_WIDTH,
        PCIE_RQ_REGIONS,
        PCIE_RQ_REGION_SIZE,
        PCIE_RQ_BLOCK_SIZE,
        PCIE_RQ_ITEM_WIDTH)
    )

    function new (string name = "virt_seq_full_speed");
        super.new(name);
    endfunction

    virtual function void init();
        super.init();
        m_usr_mfb_seq = uvm_mfb::sequence_full_speed_tx #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE,
                                                          USR_MFB_ITEM_WIDTH, USR_MFB_META_WIDTH)::type_id
                        ::create("m_usr_mfb_seq");
        m_ptr_upd_mfb_seq = uvm_mfb::sequence_full_speed_tx #(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE,
                                                              PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH,
                                                              sv_pcie_meta_pack::PCIE_RQ_META_WIDTH)::type_id
                            ::create("m_ptr_upd_mfb_seq");
    endfunction
endclass

class speed extends base;
    typedef uvm_component_registry#(test::speed, "test::speed") type_id;

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
        uvm_logic_vector_array_mfb::sequence_lib_rx #(
            PCIE_CQ_MFB_REGIONS,
            PCIE_CQ_MFB_REGION_SIZE,
            PCIE_CQ_MFB_BLOCK_SIZE,
            PCIE_CQ_MFB_ITEM_WIDTH,
            sv_pcie_meta_pack::PCIE_CQ_META_WIDTH
        )::type_id::set_inst_override(uvm_logic_vector_array_mfb::sequence_lib_rx_speed#(
            PCIE_CQ_MFB_REGIONS,
            PCIE_CQ_MFB_REGION_SIZE,
            PCIE_CQ_MFB_BLOCK_SIZE,
            PCIE_CQ_MFB_ITEM_WIDTH,
            sv_pcie_meta_pack::PCIE_CQ_META_WIDTH
        )::get_type(), "m_env.m_cq_mfb_env.*", this);

        super.build_phase(phase);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    virtual task run_phase(uvm_phase phase);
        uvm_reg_data_t pkt_cnt          [CHANNELS];
        uvm_reg_data_t byte_cnt         [CHANNELS];
        uvm_reg_data_t discard_pkt_cnt  [CHANNELS];
        uvm_reg_data_t discard_byte_cnt [CHANNELS];
        uvm_status_e   status_r;
        time end_time;
        virt_seq_full_speed #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, CHANNELS,
                              HDR_META_WIDTH, PKT_SIZE_MAX, DATA_POINTER_WIDTH, PCIE_CQ_MFB_REGIONS,
                              PCIE_CQ_MFB_REGION_SIZE, PCIE_CQ_MFB_BLOCK_SIZE, PCIE_CQ_MFB_ITEM_WIDTH) m_virt_seq;

        m_virt_seq = virt_seq_full_speed #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH,
                                           CHANNELS, HDR_META_WIDTH, PKT_SIZE_MAX, DATA_POINTER_WIDTH,
                                           PCIE_CQ_MFB_REGIONS, PCIE_CQ_MFB_REGION_SIZE, PCIE_CQ_MFB_BLOCK_SIZE,
                                           PCIE_CQ_MFB_ITEM_WIDTH)::type_id::create("m_virt_seq");

        phase.raise_objection(this);

        m_virt_seq.init();
        m_virt_seq.randomize();
        m_virt_seq.start(m_env.m_sequencer);

        end_time = $time();
        `uvm_info(this.get_full_name(), $sformatf("\n\tVirtual sequence finished (%0d ns). Scoreboard used: %0d",
                                                  end_time/1ns, m_env.m_scoreboard.used()), UVM_HIGH);

        while((end_time + 200us) > $time() && (m_env.m_scoreboard.used() != 0)) begin
            #(600ns);
        end

        for (int unsigned chan = 0; chan < CHANNELS; chan++) begin
            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].sent_packets_reg.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].sent_packets_reg.read(status_r, pkt_cnt[chan]);
            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].sent_bytes_reg.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].sent_bytes_reg.read(status_r, byte_cnt[chan]);

            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].discarded_packets_reg.write(status_r,
                                                                                                 {32'h1, 32'h1});
            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].discarded_packets_reg.read(status_r,
                                                                                                discard_pkt_cnt[chan]);
            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].discarded_bytes_reg.write(status_r,
                                                                                               {32'h1, 32'h1});
            m_env.m_regmodel_top.m_regmodel.m_regmodel_channel[chan].discarded_bytes_reg.read(status_r,
                                                                                              discard_byte_cnt[chan]);

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
