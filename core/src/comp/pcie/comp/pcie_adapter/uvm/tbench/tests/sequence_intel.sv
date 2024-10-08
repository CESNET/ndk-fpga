// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class sequence_intel#(CQ_MFB_REGIONS, CC_MFB_REGIONS, RQ_MFB_REGIONS, RC_MFB_REGIONS, CQ_MFB_REGION_SIZE, CC_MFB_REGION_SIZE, RQ_MFB_REGION_SIZE, RC_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CC_MFB_BLOCK_SIZE, RQ_MFB_BLOCK_SIZE, RC_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, AXI_DATA_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W, PCIE_MPS_DW) extends sequence_base;

    `uvm_object_param_utils(test::sequence_intel#(CQ_MFB_REGIONS, CC_MFB_REGIONS, RQ_MFB_REGIONS, RC_MFB_REGIONS, CQ_MFB_REGION_SIZE, CC_MFB_REGION_SIZE, RQ_MFB_REGION_SIZE, RC_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CC_MFB_BLOCK_SIZE, RQ_MFB_BLOCK_SIZE, RC_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, AXI_DATA_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W, PCIE_MPS_DW))

    `uvm_declare_p_sequencer(uvm_pcie_adapter::virt_sequencer#(CQ_MFB_REGIONS, CC_MFB_REGIONS, RQ_MFB_REGIONS, RC_MFB_REGIONS, CQ_MFB_REGION_SIZE, CC_MFB_REGION_SIZE, RQ_MFB_REGION_SIZE, RC_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CC_MFB_BLOCK_SIZE, RQ_MFB_BLOCK_SIZE, RC_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, AXI_DATA_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W))

    function new (string name = "sequence_intel");
        super.new(name);
    endfunction

    // Start reset sequence
    uvm_reset::sequence_start m_reset;
    // High level data sequence libraries
    uvm_logic_vector_array::sequence_lib#(CQ_MFB_ITEM_WIDTH) m_avst_down_data_lib;
    uvm_logic_vector_array::sequence_lib#(RQ_MFB_ITEM_WIDTH) m_mfb_rq_data_lib;
    uvm_logic_vector_array::sequence_lib#(CC_MFB_ITEM_WIDTH) m_mfb_cc_data_lib;

    // Credit Control Sequences
    uvm_crdt::sequence_lib m_crdt_up_lib;
    uvm_crdt::sequence_lib m_crdt_down_lib;
    // Credit Control stop Sequences
    uvm_crdt::sequence_stop m_crdt_down_stop;
    uvm_pcie_adapter::crdt_sequence #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W, PCIE_MPS_DW) m_crdt_up;

    // Low level sequence libraries
    uvm_avst::sequence_lib_tx #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W)             m_avst_up_lib;

    uvm_mfb::sequence_lib_tx  #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_ITEM_WIDTH, RC_MFB_META_W)              m_mfb_rc_lib;
    uvm_mfb::sequence_lib_tx  #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CQ_MFB_META_W)              m_mfb_cq_lib;
    uvm_sequence #(uvm_mfb::sequence_item #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_ITEM_WIDTH, RC_MFB_META_W)) m_mfb_rc_seq;
    uvm_sequence #(uvm_mfb::sequence_item #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CQ_MFB_META_W)) m_mfb_cq_seq;
    uvm_phase phase;

    logic init_done;

    virtual function void init(uvm_phase phase, uvm_pcie_adapter::tr_planner #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W) tr_plan);

        m_reset = uvm_reset::sequence_start::type_id::create("m_reset_seq");

        m_crdt_up_lib    = uvm_crdt::sequence_lib::type_id::create("m_crdt_up_lib");
        m_crdt_down_lib  = uvm_crdt::sequence_lib::type_id::create("m_crdt_down_lib");
        m_crdt_down_stop = uvm_crdt::sequence_stop::type_id::create("m_crdt_down_stop");
        m_crdt_up        = uvm_pcie_adapter::crdt_sequence#(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W, PCIE_MPS_DW)::type_id::create("m_crdt_up");

        m_avst_down_data_lib = uvm_logic_vector_array::sequence_lib#(CQ_MFB_ITEM_WIDTH)::type_id::create("m_avst_down_data_lib");
        m_mfb_rq_data_lib    = uvm_logic_vector_array::sequence_lib#(RQ_MFB_ITEM_WIDTH)::type_id::create("m_mfb_rq_data_lib");
        m_mfb_cc_data_lib    = uvm_logic_vector_array::sequence_lib#(CC_MFB_ITEM_WIDTH)::type_id::create("m_mfb_cc_data_lib");

        m_crdt_up.tr_plan = tr_plan;

        m_crdt_up_lib.init_sequence();
        m_crdt_up_lib.min_random_count = 80;
        m_crdt_up_lib.max_random_count = 100;

        m_crdt_down_lib.init_sequence();
        m_crdt_down_lib.min_random_count = 80;
        m_crdt_down_lib.max_random_count = 100;

        m_avst_down_data_lib.init_sequence();
        m_avst_down_data_lib.min_random_count = 80;
        m_avst_down_data_lib.max_random_count = 100;
        m_avst_down_data_lib.cfg = new();
        m_avst_down_data_lib.cfg.array_size_set(1, PCIE_MPS_DW);

        assert(m_avst_down_data_lib.randomize());

        m_mfb_rq_data_lib.init_sequence();
        m_mfb_rq_data_lib.min_random_count = 50;
        m_mfb_rq_data_lib.max_random_count = 100;
        m_mfb_rq_data_lib.cfg = new();
        m_mfb_rq_data_lib.cfg.array_size_set(1, PCIE_MPS_DW);

        assert(m_mfb_rq_data_lib.randomize());

        m_mfb_cc_data_lib.init_sequence();
        m_mfb_cc_data_lib.min_random_count = 50;
        m_mfb_cc_data_lib.max_random_count = 100;
        m_mfb_cc_data_lib.cfg = new();
        m_mfb_cc_data_lib.cfg.array_size_set(1, PCIE_MPS_DW);
        assert(m_mfb_cc_data_lib.randomize());

        m_avst_up_lib = uvm_avst::sequence_lib_tx#(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W)::type_id::create("m_avst_up_lib");
        m_mfb_rc_lib  = uvm_mfb::sequence_lib_tx#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_ITEM_WIDTH, RC_MFB_META_W)::type_id::create("m_mfb_rc_lib");
        m_mfb_cq_lib  = uvm_mfb::sequence_lib_tx#(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CQ_MFB_META_W)::type_id::create("m_mfb_cq_lib");

        m_avst_up_lib.init_sequence();
        m_avst_up_lib.min_random_count = 100;
        m_avst_up_lib.max_random_count = 200;

        m_mfb_rc_lib.init_sequence();
        m_mfb_rc_lib.min_random_count = 100;
        m_mfb_rc_lib.max_random_count = 200;
        m_mfb_rc_seq = m_mfb_rc_lib;

        m_mfb_cq_lib.init_sequence();
        m_mfb_cq_lib.min_random_count = 100;
        m_mfb_cq_lib.max_random_count = 200;
        m_mfb_cq_seq = m_mfb_cq_lib;

        this.phase = phase;

    endfunction

    virtual task run_crdt_up();
        forever begin
            assert(m_crdt_up.randomize());
            m_crdt_up.start(p_sequencer.m_crdt_up_sqr);
        end
    endtask

    virtual task run_crdt_down();
        forever begin
            assert(m_crdt_down_lib.randomize());
            m_crdt_down_lib.start(p_sequencer.m_crdt_down_sqr);
        end
    endtask

    virtual task run_avst_up();
        forever begin
            assert(m_avst_up_lib.randomize());
            m_avst_up_lib.start(p_sequencer.m_avst_up_rdy_sqr);
        end
    endtask

    virtual task run_mfb_rc();
        forever begin
            assert(m_mfb_rc_seq.randomize());
            m_mfb_rc_seq.start(p_sequencer.m_mfb_rc_dst_rdy_sqr);
        end
    endtask

    virtual task run_mfb_cq();
        forever begin
            assert(m_mfb_cq_seq.randomize());
            m_mfb_cq_seq.start(p_sequencer.m_mfb_cq_dst_rdy_sqr);
        end
    endtask

    virtual task run_reset();
        assert(m_reset.randomize());
        m_reset.start(p_sequencer.m_reset);
    endtask

    virtual task crdt_down_stop();
        assert(m_crdt_down_stop.randomize());
        m_crdt_down_stop.start(p_sequencer.m_crdt_down_sqr);
        init_done = 1'b1;
    endtask

    task body();

        fork
            run_reset();
            crdt_down_stop();
        join_none

        #(100ns);
        fork
            run_crdt_up();
        join_none
        wait(init_done);

        fork
            run_mfb_rc();
            run_mfb_cq();
            run_avst_up();
            run_crdt_down();
        join_none

        fork
            run_avst_down_data();
            run_mfb_rq_data();
            run_mfb_cc_data();
        join

    endtask

    virtual task run_avst_down_data();
        m_avst_down_data_lib.start(p_sequencer.m_avst_down_data_sqr);
    endtask

    virtual task run_mfb_rq_data();
        m_mfb_rq_data_lib.start(p_sequencer.m_rq_mfb_data_sqr);
    endtask

    virtual task run_mfb_cc_data();
        m_mfb_cc_data_lib.start(p_sequencer.m_cc_mfb_data_sqr);
    endtask

endclass
