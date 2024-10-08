// sequence.sv:  virtual sequence
// Copyright (C) 2022-2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class virt_seq #(
    int unsigned USR_MFB_REGIONS,
    int unsigned USR_MFB_REGION_SIZE,
    int unsigned USR_MFB_BLOCK_SIZE,
    int unsigned USR_MFB_ITEM_WIDTH,
    int unsigned CHANNELS,
    int unsigned HDR_META_WIDTH,
    int unsigned PKT_SIZE_MAX
) extends uvm_sequence;

    `uvm_object_param_utils(test::virt_seq #(
        USR_MFB_REGIONS,
        USR_MFB_REGION_SIZE,
        USR_MFB_BLOCK_SIZE,
        USR_MFB_ITEM_WIDTH,
        CHANNELS,
        HDR_META_WIDTH,
        PKT_SIZE_MAX
    ))

    `uvm_declare_p_sequencer(uvm_tx_dma_calypte::sequencer #(
        USR_MFB_REGIONS,
        USR_MFB_REGION_SIZE,
        USR_MFB_BLOCK_SIZE,
        USR_MFB_ITEM_WIDTH,
        CHANNELS,
        HDR_META_WIDTH,
        PKT_SIZE_MAX
    ))

    localparam USR_MFB_META_WIDTH = HDR_META_WIDTH + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);

    uvm_reset::sequence_start                                                                                                                  m_reset_seq;
    uvm_tx_dma_calypte::sequence_simple                                                                                                        m_channel_seq [CHANNELS];
    uvm_sequence #(uvm_mfb::sequence_item #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, USR_MFB_META_WIDTH)) m_usr_mfb_seq;

    local logic [CHANNELS-1:0] m_done;

    function new (string name = "virt_seq");
        super.new(name);
    endfunction

    virtual function void init();
        uvm_mfb::sequence_lib_tx #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, USR_MFB_META_WIDTH) m_usr_mfb_seq_lib;

        m_reset_seq = uvm_reset::sequence_start::type_id::create("m_reset_seq");

        for (int unsigned it = 0; it < CHANNELS; it++) begin
            m_channel_seq[it] = uvm_tx_dma_calypte::sequence_simple::type_id::create($sformatf("m_channel_seq_%0d", it));
            m_channel_seq[it].m_packet_size_max = PKT_SIZE_MAX;
        end

        m_usr_mfb_seq_lib = uvm_mfb::sequence_lib_tx #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, USR_MFB_META_WIDTH)::type_id::create("m_usr_mfb_seq_lib");
        m_usr_mfb_seq_lib.init_sequence();
        m_usr_mfb_seq = m_usr_mfb_seq_lib;   // NOTE: WHY????!
    endfunction

    virtual task run_mfb();
        forever begin
            assert(m_usr_mfb_seq.randomize());
            m_usr_mfb_seq.start(p_sequencer.m_usr_mfb_sqcr);
        end
    endtask

    virtual task run_reset();
        assert(m_reset_seq.randomize());
        m_reset_seq.start(p_sequencer.m_reset_sqcr);
    endtask

    virtual task run_channels();
        uvm_common::sequence_cfg_transactions seq_cfg;

        seq_cfg = new();
        seq_cfg.transactions_min = 3000;
        seq_cfg.transactions_max = 7000;
        assert(seq_cfg.randomize());
        #(200ns);

        for (int unsigned it = 0; it < CHANNELS; it++) begin
            fork
                automatic int unsigned index = it;
                begin
                    uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.m_packet_sqcr[index], "", "state", seq_cfg);

                    assert(m_channel_seq[index].randomize());
                    m_channel_seq[index].start(p_sequencer.m_packet_sqcr[index]);
                    m_done[index] = 1;
                    `uvm_info(this.get_full_name(), $sformatf("\n\t Main packet sequence done on channel %0d", index), UVM_LOW);
                end
            join_none
        end
    endtask

    task body();
        m_done = 0;

        fork
            run_reset();
            run_channels();
        join_none

        #(200ns);

        fork
            run_mfb();
        join_none

        wait((& m_done) == 1);
    endtask
endclass
