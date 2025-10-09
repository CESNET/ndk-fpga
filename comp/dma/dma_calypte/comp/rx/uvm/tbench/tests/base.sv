//-- base.sv: Basic test
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class base#(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH, CHANNELS, PKT_SIZE_MAX, MI_WIDTH, DEVICE) extends uvm_test;
    typedef uvm_component_registry#(test::base#(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH, CHANNELS, PKT_SIZE_MAX, MI_WIDTH, DEVICE), "test::base") type_id;


    uvm_dma_ll::env #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH, CHANNELS, PKT_SIZE_MAX, MI_WIDTH, DEVICE) m_env;
    localparam USR_MFB_META_WIDTH = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);

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
        m_env = uvm_dma_ll::env #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH, CHANNELS, PKT_SIZE_MAX, MI_WIDTH, DEVICE)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    virtual task run_phase(uvm_phase phase);
        time end_time;
        virt_seq #(USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH, CHANNELS) m_vseq;
        uvm_reg_data_t pkt_cnt          [CHANNELS];
        uvm_reg_data_t byte_cnt         [CHANNELS];
        uvm_reg_data_t discard_pkt_cnt  [CHANNELS];
        uvm_reg_data_t discard_byte_cnt [CHANNELS];
        uvm_status_e   status_r;

        //CREATE SEQUENCES
        m_vseq = virt_seq #(USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH, CHANNELS)::type_id::create("m_vseq");

        //RISE OBJECTION
        phase.raise_objection(this);

        m_vseq.init(m_env.m_regmodel.m_regmodel);
        m_vseq.randomize();
        m_vseq.start(m_env.m_sequencer);

        end_time = $time();
        `uvm_info(this.get_full_name(), $sformatf("\n\tVirtual sequence finished (%0d ns). Environment used: %0d", end_time/1ns, m_env.used()), UVM_LOW);

        #(2us); //wait to send last packet to DUT. This prevent when last packet is not DUT yet and m_env.used() is called.
        // The last packet can be stored in MFB sequence and environment doesnt have to see it.
        // this means that m_env.used() can return 0 and last packet can be send to DUT.
        while((end_time + 200us) > $time() && m_env.used() != 0) begin
            #(600ns);
            `uvm_info(this.get_full_name(), "\n\tWaiting after virtual sequence finished.", UVM_MEDIUM);
        end

        for (int unsigned chan = 0; chan < CHANNELS; chan++) begin
            m_env.m_regmodel.m_regmodel.channel[chan].sent_packets_cnt.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel.m_regmodel.channel[chan].sent_packets_cnt.read(status_r, pkt_cnt[chan]);
            m_env.m_regmodel.m_regmodel.channel[chan].sent_bytes_cnt.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel.m_regmodel.channel[chan].sent_bytes_cnt.read(status_r, byte_cnt[chan]);

            m_env.m_regmodel.m_regmodel.channel[chan].disc_packets_cnt.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel.m_regmodel.channel[chan].disc_packets_cnt.read(status_r, discard_pkt_cnt[chan]);
            m_env.m_regmodel.m_regmodel.channel[chan].disc_bytes_cnt.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel.m_regmodel.channel[chan].disc_bytes_cnt.read(status_r, discard_byte_cnt[chan]);

            m_env.m_scoreboard.m_pkt_cnt[chan]          = pkt_cnt[chan];
            m_env.m_scoreboard.m_byte_cnt[chan]         = byte_cnt[chan];
            m_env.m_scoreboard.m_discard_pkt_cnt[chan]  = discard_pkt_cnt[chan];
            m_env.m_scoreboard.m_discard_byte_cnt[chan] = discard_byte_cnt[chan];
        end

        phase.drop_objection(this);
    endtask
endclass
