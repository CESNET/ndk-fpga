// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_cxs2_rx_mvb #(RX_MVB_ITEM_W, USERMETA_W) extends uvm_sequence #(uvm_logic_vector::sequence_item #(RX_MVB_ITEM_W));
    `uvm_object_param_utils(test::sequence_cxs2_rx_mvb #(RX_MVB_ITEM_W, USERMETA_W))

    // Constructor - creates new instance of this class
    function new(string name = "sequence_cxs2_rx_mvb");
        super.new(name);
    endfunction

    // Generates transactions
    task body;
        `uvm_info(get_full_name(), "sequence_cxs2_rx_mvb is running", UVM_DEBUG)
        forever begin
            // Generate random request
            `uvm_do_with(req,
            {
                // DEBUG settings:
                //data[USERMETA_W] == 1'b0; // discard
                //data[USERMETA_W+1+MOD_W-1 : USERMETA_W+1] == 16; // MOD SOF size
                //data[USERMETA_W+1+MOD_W] == 1'b1; // MOD SOF enable
                //data[USERMETA_W+MOD_W+2] == 1'b0; // MOD SOF type
                //data[USERMETA_W+MOD_W+3+MOD_W] == 1'b1; // MOD EOF enable
                //data[USERMETA_W+MOD_W+3+MOD_W+1] == 1'b1; // MOD EOF type
            })
        end
    endtask

endclass

class virt_sequence #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, FRAME_SIZE_MIN, FRAME_SIZE_MAX) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, FRAME_SIZE_MIN, FRAME_SIZE_MAX))
    `uvm_declare_p_sequencer(uvm_mfb_crossbarx_stream2::virt_sequencer #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                                                                                       m_reset;
    test::sequence_cxs2_rx_mvb #(RX_MVB_ITEM_W, USERMETA_W)                                                         m_mvb_data_seq;
    uvm_logic_vector_array::sequence_lib #(RX_MFB_ITEM_W)                                                           m_mfb_data_sq_lib;
    uvm_logic_vector::sequence_endless #(USERMETA_W)                                                                m_mfb_meta_sq;

    uvm_sequence#(uvm_mfb::sequence_item#(TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, USERMETA_W)) m_mfb_rdy_seq;
    uvm_mfb::sequence_lib_tx#(TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, USERMETA_W)              m_mfb_rdy_lib;

    uvm_sequence#(uvm_mvb::sequence_item#(TX_MFB_REGIONS, USERMETA_W)) m_mvb_rdy_seq;
    uvm_mvb::sequence_lib_tx#(TX_MFB_REGIONS, USERMETA_W)              m_mvb_rdy_lib;

    uvm_phase phase;

    virtual function void init(uvm_phase phase);

        m_reset                  = uvm_reset::sequence_start::type_id::create("m_reset_seq");
        m_reset.reset.length_min = 10;
        m_mfb_data_sq_lib   = uvm_logic_vector_array::sequence_lib #(RX_MFB_ITEM_W)::type_id::create("m_mfb_data_sq_lib");
        m_mfb_meta_sq       = uvm_logic_vector::sequence_endless #(USERMETA_W)::type_id::create("m_mfb_meta_sq");
        m_mvb_data_seq      = test::sequence_cxs2_rx_mvb #(RX_MVB_ITEM_W, USERMETA_W)::type_id::create("m_mvb_data_seq");

        m_mfb_rdy_lib       = uvm_mfb::sequence_lib_tx#(TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, USERMETA_W)::type_id::create("m_mfb_rdy_lib");
        m_mvb_rdy_lib       = uvm_mvb::sequence_lib_tx#(TX_MFB_REGIONS, USERMETA_W)::type_id::create("m_mvb_rdy_lib");

        m_mfb_data_sq_lib.init_sequence();
        m_mfb_data_sq_lib.cfg = new();
        m_mfb_data_sq_lib.cfg.array_size_set(FRAME_SIZE_MIN, FRAME_SIZE_MAX);
        m_mfb_data_sq_lib.min_random_count = 100;
        m_mfb_data_sq_lib.max_random_count = 200;
        m_mfb_data_sq_lib.randomize();

        m_mfb_rdy_lib.init_sequence();
        m_mfb_rdy_lib.min_random_count = 200;
        m_mfb_rdy_lib.max_random_count = 300;
        m_mfb_rdy_seq = m_mfb_rdy_lib;

        m_mvb_rdy_lib.init_sequence();
        m_mvb_rdy_lib.min_random_count = 200;
        m_mvb_rdy_lib.max_random_count = 300;
        m_mvb_rdy_seq = m_mvb_rdy_lib;

        this.phase = phase;

    endfunction

    virtual task mfb_rdy_seq();
        //RUN TX Sequencer
        forever begin
            m_mfb_rdy_seq.randomize();
            m_mfb_rdy_seq.start(p_sequencer.m_mfb_rdy_sqr);
        end
    endtask

    virtual task mvb_rdy_seq();
        //RUN TX Sequencer
        forever begin
            m_mvb_rdy_seq.randomize();
            m_mvb_rdy_seq.start(p_sequencer.m_mvb_rdy_sqr);
        end
    endtask

    virtual task run_reset();
        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset_sqr);
    endtask

    task body();

        fork
            run_reset();
        join_none

        #(100ns);

        //RUN MFB and MVB TX SEQUENCE
        fork
            mfb_rdy_seq();
            mvb_rdy_seq();
        join_none

        fork
            m_mfb_data_sq_lib.start(p_sequencer.m_mfb_data_sqr);
            begin
                m_mfb_meta_sq.randomize();
                m_mfb_meta_sq.start(p_sequencer.m_mfb_meta_sqr);
            end
            begin
                m_mvb_data_seq.randomize();
                m_mvb_data_seq.start(p_sequencer.m_mvb_data_sqr);
            end
        join_any
        `uvm_info(this.get_full_name(),"\n\tSEQ DONE!", UVM_NONE);
    endtask

endclass
