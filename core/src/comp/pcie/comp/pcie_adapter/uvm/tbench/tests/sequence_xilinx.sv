// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

virtual class sequence_base extends uvm_sequence;
    `uvm_object_utils(test::sequence_base)

    function new (string name = "nice_sequence");
        super.new(name);
    endfunction

    pure virtual function void init(uvm_phase phase, uvm_pcie_adapter::tr_planner #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W) tr_plan);

endclass

class sequence_xilinx#(CQ_MFB_REGIONS, CC_MFB_REGIONS, RQ_MFB_REGIONS, RC_MFB_REGIONS, CQ_MFB_REGION_SIZE, CC_MFB_REGION_SIZE, RQ_MFB_REGION_SIZE, RC_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CC_MFB_BLOCK_SIZE, RQ_MFB_BLOCK_SIZE, RC_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, AXI_DATA_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W) extends sequence_base;

    `uvm_object_param_utils(test::sequence_xilinx#(CQ_MFB_REGIONS, CC_MFB_REGIONS, RQ_MFB_REGIONS, RC_MFB_REGIONS, CQ_MFB_REGION_SIZE, CC_MFB_REGION_SIZE, RQ_MFB_REGION_SIZE, RC_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CC_MFB_BLOCK_SIZE, RQ_MFB_BLOCK_SIZE, RC_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, AXI_DATA_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W))

    `uvm_declare_p_sequencer(uvm_pcie_adapter::virt_sequencer#(CQ_MFB_REGIONS, CC_MFB_REGIONS, RQ_MFB_REGIONS, RC_MFB_REGIONS, CQ_MFB_REGION_SIZE, CC_MFB_REGION_SIZE, RQ_MFB_REGION_SIZE, RC_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CC_MFB_BLOCK_SIZE, RQ_MFB_BLOCK_SIZE, RC_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, AXI_DATA_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W))

    function new (string name = "sequence_xilinx");
        super.new(name);
    endfunction

    // Start reset sequence
    uvm_reset::sequence_start m_reset;
    // High level data sequence libraries
    uvm_logic_vector_array::sequence_lib#(CQ_MFB_ITEM_WIDTH) m_axi_cq_data_lib;
    uvm_logic_vector_array::sequence_lib#(RC_MFB_ITEM_WIDTH) m_axi_rc_data_lib;
    uvm_logic_vector_array::sequence_lib#(RQ_MFB_ITEM_WIDTH) m_mfb_rq_data_lib;
    uvm_logic_vector_array::sequence_lib#(CC_MFB_ITEM_WIDTH) m_mfb_cc_data_lib;

    // Metadata sequences
    uvm_logic_vector::sequence_endless#(RQ_MFB_META_W)    m_mfb_rq_meta_sq;
    uvm_logic_vector::sequence_endless#(CC_MFB_META_W)    m_mfb_cc_meta_sq;

    // Low level sequence libraries
    uvm_axi::sequence_lib_tx  #(AXI_DATA_WIDTH, AXI_CCUSER_WIDTH, CC_MFB_REGIONS) m_axi_cc_lib;
    uvm_axi::sequence_lib_tx  #(AXI_DATA_WIDTH, AXI_RQUSER_WIDTH, RQ_MFB_REGIONS) m_axi_rq_lib;
    uvm_mfb::sequence_lib_tx  #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_ITEM_WIDTH, RC_MFB_META_W) m_mfb_rc_lib;
    uvm_mfb::sequence_lib_tx  #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CQ_MFB_META_W) m_mfb_cq_lib;
    uvm_phase phase;

    virtual function void init(uvm_phase phase, uvm_pcie_adapter::tr_planner #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W) tr_plan);

        m_reset = uvm_reset::sequence_start::type_id::create("m_reset_seq");

        m_axi_cq_data_lib    = uvm_logic_vector_array::sequence_lib#(CQ_MFB_ITEM_WIDTH)::type_id::create("m_axi_cq_data_lib");
        m_axi_rc_data_lib    = uvm_logic_vector_array::sequence_lib#(RC_MFB_ITEM_WIDTH)::type_id::create("m_axi_rc_data_lib");
        m_mfb_rq_data_lib    = uvm_logic_vector_array::sequence_lib#(RQ_MFB_ITEM_WIDTH)::type_id::create("m_mfb_rq_data_lib");
        m_mfb_cc_data_lib    = uvm_logic_vector_array::sequence_lib#(CC_MFB_ITEM_WIDTH)::type_id::create("m_mfb_cc_data_lib");

        m_axi_cq_data_lib.init_sequence();
        m_axi_cq_data_lib.min_random_count = 50;
        m_axi_cq_data_lib.max_random_count = 100;
        m_axi_cq_data_lib.randomize();

        m_axi_rc_data_lib.init_sequence();
        m_axi_rc_data_lib.min_random_count = 50;
        m_axi_rc_data_lib.max_random_count = 100;
        m_axi_rc_data_lib.randomize();

        m_mfb_rq_data_lib.init_sequence();
        m_mfb_rq_data_lib.min_random_count = 50;
        m_mfb_rq_data_lib.max_random_count = 100;
        m_mfb_rq_data_lib.randomize();

        m_mfb_cc_data_lib.init_sequence();
        m_mfb_cc_data_lib.min_random_count = 50;
        m_mfb_cc_data_lib.max_random_count = 100;
        m_mfb_cc_data_lib.randomize();

        m_mfb_rq_meta_sq    = uvm_logic_vector::sequence_endless#(RQ_MFB_META_W)::type_id::create("m_mfb_rq_meta_sq");
        m_mfb_cc_meta_sq    = uvm_logic_vector::sequence_endless#(CC_MFB_META_W)::type_id::create("m_mfb_cc_meta_sq");

        m_axi_cc_lib  = uvm_axi::sequence_lib_tx#(AXI_DATA_WIDTH, AXI_CCUSER_WIDTH, CC_MFB_REGIONS)::type_id::create("m_axi_cc_lib");
        m_axi_rq_lib  = uvm_axi::sequence_lib_tx#(AXI_DATA_WIDTH, AXI_RQUSER_WIDTH, RQ_MFB_REGIONS)::type_id::create("m_axi_rq_lib");
        m_mfb_rc_lib  = uvm_mfb::sequence_lib_tx#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_ITEM_WIDTH, RC_MFB_META_W)::type_id::create("m_mfb_rc_lib");
        m_mfb_cq_lib  = uvm_mfb::sequence_lib_tx#(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CQ_MFB_META_W)::type_id::create("m_mfb_cq_lib");

        m_axi_cc_lib.init_sequence();
        m_axi_cc_lib.min_random_count = 100;
        m_axi_cc_lib.max_random_count = 200;

        m_axi_rq_lib.init_sequence();
        m_axi_rq_lib.min_random_count = 100;
        m_axi_rq_lib.max_random_count = 200;

        m_mfb_rc_lib.init_sequence();
        m_mfb_rc_lib.min_random_count = 100;
        m_mfb_rc_lib.max_random_count = 200;

        m_mfb_cq_lib.init_sequence();
        m_mfb_cq_lib.min_random_count = 100;
        m_mfb_cq_lib.max_random_count = 200;

        this.phase = phase;

    endfunction

    virtual task run_axi_cc();
        forever begin
            assert(m_axi_cc_lib.randomize());
            m_axi_cc_lib.start(p_sequencer.m_axi_cc_rdy_sqr);
        end
    endtask

    virtual task run_axi_rq();
        forever begin
            assert(m_axi_rq_lib.randomize());
            m_axi_rq_lib.start(p_sequencer.m_axi_rq_rdy_sqr);
        end
    endtask

    virtual task run_mfb_rc();
        forever begin
            assert(m_mfb_rc_lib.randomize());
            m_mfb_rc_lib.start(p_sequencer.m_mfb_rc_dst_rdy_sqr);
        end
    endtask

    virtual task run_mfb_cq();
        forever begin
            assert(m_mfb_cq_lib.randomize());
            m_mfb_cq_lib.start(p_sequencer.m_mfb_cq_dst_rdy_sqr);
        end
    endtask

    virtual task run_reset();
        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset);
    endtask


    task body();

        fork
            run_reset();
        join_none

        #(100ns);

        fork
            run_mfb_rc();
            run_mfb_cq();
            run_axi_cc();
            run_axi_rq();
        join_none

        fork
            run_axi_cq_data();
            run_axi_rc_data();
            run_mfb_rq_data();
            forever begin 
                m_mfb_rq_meta_sq.randomize();
                m_mfb_rq_meta_sq.start(p_sequencer.m_rq_mfb_meta_sqr);
            end
            run_mfb_cc_data();
            forever begin 
                m_mfb_cc_meta_sq.randomize();
                m_mfb_cc_meta_sq.start(p_sequencer.m_cc_mfb_meta_sqr);
            end
        join_any

    endtask

    virtual task run_axi_cq_data();
        m_axi_cq_data_lib.start(p_sequencer.m_axi_cq_data_sqr);
    endtask

    virtual task run_axi_rc_data();
        m_axi_rc_data_lib.start(p_sequencer.m_axi_rc_data_sqr);
    endtask

    virtual task run_mfb_rq_data();
        m_mfb_rq_data_lib.start(p_sequencer.m_rq_mfb_data_sqr);
    endtask

    virtual task run_mfb_cc_data();
        m_mfb_cc_data_lib.start(p_sequencer.m_cc_mfb_data_sqr);
    endtask

endclass
