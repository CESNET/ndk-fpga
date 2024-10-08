//-- base.sv: Basic test
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class base#(USER_REGIONS, USER_REGION_SIZE, USER_BLOCK_SIZE, USER_ITEM_WIDTH, PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH, CHANNELS, PKT_SIZE_MAX, MI_WIDTH, DEVICE) extends uvm_test;
    typedef uvm_component_registry#(test::base#(USER_REGIONS, USER_REGION_SIZE, USER_BLOCK_SIZE, USER_ITEM_WIDTH, PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH, CHANNELS, PKT_SIZE_MAX, MI_WIDTH, DEVICE), "test::base") type_id;


    uvm_dma_ll::env #(USER_REGIONS, USER_REGION_SIZE, USER_BLOCK_SIZE, USER_ITEM_WIDTH, PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH, CHANNELS, PKT_SIZE_MAX, MI_WIDTH, DEVICE) m_env;
    localparam USER_META_WIDTH = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);

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
        m_env = uvm_dma_ll::env #(USER_REGIONS, USER_REGION_SIZE, USER_BLOCK_SIZE, USER_ITEM_WIDTH, PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH, CHANNELS, PKT_SIZE_MAX, MI_WIDTH, DEVICE)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    virtual task run_phase(uvm_phase phase);
        time end_time;
        virt_seq #(PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH, CHANNELS) m_vseq;
        uvm_reg_data_t pkt_cnt          [CHANNELS];
        uvm_reg_data_t byte_cnt         [CHANNELS];
        uvm_reg_data_t discard_pkt_cnt  [CHANNELS];
        uvm_reg_data_t discard_byte_cnt [CHANNELS];
        uvm_status_e   status_r;

        //CREATE SEQUENCES
        m_vseq = virt_seq #(PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH, CHANNELS)::type_id::create("m_vseq");

        //RISE OBJECTION
        phase.raise_objection(this);

        m_vseq.init(m_env.m_regmodel.m_regmodel);
        m_vseq.randomize();
        m_vseq.start(m_env.m_sequencer);

        end_time = $time();
        `uvm_info(this.get_full_name(), $sformatf("\n\tVirtual sequence finished (%0d ns). Environment used: %0d", end_time/1ns, m_env.used()), UVM_LOW);

        while((end_time + 200us) > $time() && (m_env.used() != 0)) begin
            #(600ns);
            `uvm_info(this.get_full_name(), "\n\tWaiting after virtual sequence finished.", UVM_MEDIUM);
        end

        #(1us)

        for (int unsigned chan = 0; chan < CHANNELS; chan++) begin
            m_env.m_regmodel.m_regmodel.channel[chan].sent_packets_cnt.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel.m_regmodel.channel[chan].sent_packets_cnt.read(status_r, pkt_cnt[chan]);
            m_env.m_regmodel.m_regmodel.channel[chan].sent_bytes_cnt.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel.m_regmodel.channel[chan].sent_bytes_cnt.read(status_r, byte_cnt[chan]);

            m_env.m_regmodel.m_regmodel.channel[chan].disc_packets_cnt.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel.m_regmodel.channel[chan].disc_packets_cnt.read(status_r, discard_pkt_cnt[chan]);
            m_env.m_regmodel.m_regmodel.channel[chan].disc_bytes_cnt.write(status_r, {32'h1, 32'h1});
            m_env.m_regmodel.m_regmodel.channel[chan].disc_bytes_cnt.read(status_r, discard_byte_cnt[chan]);

            m_env.sc.pkt_cnt[chan]          = pkt_cnt[chan];
            m_env.sc.byte_cnt[chan]         = byte_cnt[chan];
            m_env.sc.discard_pkt_cnt[chan]  = discard_pkt_cnt[chan];
            m_env.sc.discard_byte_cnt[chan] = discard_byte_cnt[chan];
        end

        phase.drop_objection(this);
    endtask
endclass
