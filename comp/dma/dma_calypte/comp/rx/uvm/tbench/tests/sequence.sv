//-- sequence.sv:  virtual sequence
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class virt_seq#(USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH, CHANNELS) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_seq#(USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH,  CHANNELS))
    `uvm_declare_p_sequencer(uvm_dma_ll::sequencer#(USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH, CHANNELS))

    function new (string name = "virt_seq");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                                                                                                                 m_reset_seq;
    uvm_logic_vector_array::sequence_lib #(USR_MFB_ITEM_WIDTH)                                                                                m_usr_mfb_seq;
    uvm_dma_ll::reg_sequence#(CHANNELS)                                                                                                       m_reg_seq;
    uvm_sequence#(uvm_mfb::sequence_item #(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH)) m_pcie_rq_mfb_seq;

    local logic m_done;

    virtual function void init(uvm_dma_ll::regmodel#(CHANNELS) m_regmodel);
        uvm_mfb::sequence_lib_tx#(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH) m_pcie_rq_mfb_seq_lib;

        m_reset_seq = uvm_reset::sequence_start::type_id::create("rst_seq");

        m_usr_mfb_seq = uvm_logic_vector_array::sequence_lib#(USR_MFB_ITEM_WIDTH)::type_id::create("m_usr_mfb_seq");
        m_usr_mfb_seq.init_sequence();
        m_usr_mfb_seq.min_random_count = 80;
        m_usr_mfb_seq.max_random_count = 100;
        m_usr_mfb_seq.cfg = new();
        m_usr_mfb_seq.cfg.array_size_set(60,PKT_SIZE_MAX);

        m_reg_seq =  uvm_dma_ll::reg_sequence#(CHANNELS)::type_id::create("m_reg_seq");
        m_reg_seq.m_regmodel = m_regmodel;

        m_pcie_rq_mfb_seq_lib  = uvm_mfb::sequence_lib_tx#(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH)::type_id::create();
        m_pcie_rq_mfb_seq_lib.init_sequence();
        m_pcie_rq_mfb_seq = m_pcie_rq_mfb_seq_lib;
    endfunction

    virtual task run_mfb();
        forever begin
            assert(m_pcie_rq_mfb_seq.randomize());
            m_pcie_rq_mfb_seq.start(p_sequencer.m_pcie_rq_mfb_sqcr);
        end
    endtask

    virtual task run_reset();
        m_reset_seq.randomize();
        m_reset_seq.start(p_sequencer.m_reset_sqcr);
    endtask

    function void pre_randomize();
         m_usr_mfb_seq.randomize();
         m_reg_seq.randomize();
    endfunction

    task body();
        m_done = 0;

        fork
            run_reset();
            begin
                #(200ns)
                m_reg_seq.start(null);
            end
        join_none

        #(50ns)

        fork
            begin
                m_usr_mfb_seq.start(p_sequencer.m_usr_mfb_sqcr.m_data_sqcr);
                m_done = 1;
            end

            run_mfb();
        join_any

        wait((& m_done) == 1);
    endtask
endclass
