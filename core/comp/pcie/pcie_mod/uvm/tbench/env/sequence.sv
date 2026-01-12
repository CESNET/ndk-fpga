// sequence.sv : virtual sequence
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_base #(
    int unsigned RC_MFB_REGIONS,
    int unsigned RC_MFB_REGION_SIZE,
    int unsigned RC_MFB_BLOCK_SIZE,

    int unsigned CQ_MFB_REGIONS,
    int unsigned CQ_MFB_REGION_SIZE,
    int unsigned CQ_MFB_BLOCK_SIZE,

    int unsigned CC_MFB_REGIONS,
    int unsigned CC_MFB_REGION_SIZE,
    int unsigned CC_MFB_BLOCK_SIZE,

    int unsigned ITEM_WIDTH,
    int unsigned DMA_PORTS,
    int unsigned PCIE_CONS,
    int unsigned PCIE_ENDPOINTS
) extends uvm_sequence;
    `uvm_object_param_utils(uvm_pcie_top::sequence_base#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE,  CQ_MFB_BLOCK_SIZE,
                                                         CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, DMA_PORTS, PCIE_CONS, PCIE_ENDPOINTS))

     `uvm_declare_p_sequencer(uvm_pcie_top::sequencer#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE,
                                                       CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE,
                                                       ITEM_WIDTH,  DMA_PORTS, PCIE_ENDPOINTS))

    protected int unsigned stop;
    protected logic [DMA_PORTS-1:0] rx_stop[PCIE_ENDPOINTS];
    protected logic tx_stop;

    //RQ
    uvm_dma::sequence_dma_rq_lib#(DMA_PORTS) dma_rq[PCIE_ENDPOINTS][DMA_PORTS];
    //RC
    uvm_sequence #(uvm_mfb::sequence_item #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, ITEM_WIDTH, sv_pcie_meta_pack::PCIE_RC_META_WIDTH)) m_mfb_rc[PCIE_ENDPOINTS][DMA_PORTS];
    uvm_sequence #(uvm_mvb::sequence_item #(RC_MFB_REGIONS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH))                               m_mvb_rc[PCIE_ENDPOINTS][DMA_PORTS];
    //CQ
    uvm_sequence #(uvm_mfb::sequence_item #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)) m_mfb_cq[PCIE_ENDPOINTS][DMA_PORTS];
    //CC
    uvm_sequence #(uvm_pcie::header)                                                                                           m_dma_cc[PCIE_ENDPOINTS][DMA_PORTS];
    //uvm_pcie_dma_cq::sequence_resp                                                                                             m_dma_cc[PCIE_ENDPOINTS][DMA_PORTS];

    //MI
    uvm_pcie_top::mi_cc_sequence #(32, 32) mi_seq[PCIE_ENDPOINTS];

    //PCIE
    // uvm_pcie::sequence_base
    uvm_pcie::sequence_request_lib pcie_seq_cq[PCIE_ENDPOINTS];
    uvm_pcie::sequence_comp_lib    pcie_seq_rc[PCIE_ENDPOINTS];

    // Start reset sequence
    uvm_reset::sequence_start m_dma_reset;
    uvm_reset::sequence_start m_mi_reset;
    uvm_reset::sequence_start m_pcie_sysrst_n;

    //STOP SEQUENCE
    //sequences_cfg_sync#(int unsigned NUM) sync;

    function new(string name = "sequence_simple_rx_base");
        super.new(name);
        for (int unsigned it = 0; it < PCIE_ENDPOINTS; it++) begin
            rx_stop[it] = 0;
        end
    endfunction

    function void stop_send();
        tx_stop = 0;
    endfunction

    virtual function void init(
        uvm_pcie_top::sequencer#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE,
                                 CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE,
                                 ITEM_WIDTH, DMA_PORTS, PCIE_ENDPOINTS) p_sequencer);

        for (int unsigned pcie = 0; pcie < PCIE_ENDPOINTS; pcie++) begin
             string pcie_string;
             pcie_string.itoa(pcie);

             for (int dma = 0; dma < DMA_PORTS; dma++) begin
                string dma_string = {pcie_string, $sformatf("_%0d", dma)};
                uvm_mfb::sequence_lib_tx  #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)              m_mfb_cq_lib;

                //RQ
                dma_rq[pcie][dma] = uvm_dma::sequence_dma_rq_lib#(DMA_PORTS)::type_id::create("dma_rq", p_sequencer.m_dma_rq[pcie][dma]);
                dma_rq[pcie][dma].init_sequence();
                dma_rq[pcie][dma].min_random_count = 100;
                dma_rq[pcie][dma].max_random_count = 200;

                //RC

                //CQ
                //m_mfb_cq_lib  = uvm_mfb::sequence_lib_tx#(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, CQ_MFB_META_W)::type_id::create({"m_mfb_cq_lib_", dma_string}, p_sequencer.m_dma_cq[pcie][dma]);
                //m_mfb_cq_lib.init_sequence();
                //m_mfb_cq_lib.min_random_count = 100;
                //m_mfb_cq_lib.max_random_count = 200;
                //m_mfb_cq[pcie][dma] = m_mfb_cq_lib;

                //CC
                //m_dma_cc[pcie][dma] = uvm_pcie_dma_cq::sequence_resp::type_id::create({"m_dma_seq_", dma_string}, p_sequencer.m_dma_cc[pcie][dma]);
                m_dma_cc[pcie][dma] = uvm_pcie::sequence_comp::type_id::create({"m_dma_seq_", dma_string}, p_sequencer.m_dma_cc[pcie][dma]);
             end

             //MI interface
             mi_seq[pcie] = uvm_pcie_top::mi_cc_sequence #(32, 32)::type_id::create({"mi_seq_", pcie_string}, p_sequencer.m_mi_sqr[pcie]);

             //PCIE
             pcie_seq_rc[pcie] = uvm_pcie::sequence_comp_lib::type_id::create({"pcie_seq_rc_", pcie_string}, p_sequencer.m_pcie_rc[pcie]);
             pcie_seq_rc[pcie].init_sequence();

             pcie_seq_cq[pcie] = uvm_pcie::sequence_request_lib::type_id::create({"pcie_seq_cq_", pcie_string}, p_sequencer.m_pcie_cq[pcie]);
             pcie_seq_cq[pcie].init_sequence();
             //pcie_seq[pcie] = new(); //uvm_pcie::sequence_base::type_id::create({"pcie_seq_", pcie_string}, p_sequencer.m_pcie[pcie]);
        end

        m_dma_reset     = uvm_reset::sequence_start::type_id::create("m_dma_reset");
        m_mi_reset      = uvm_reset::sequence_start::type_id::create("m_mi_reset");
        m_pcie_sysrst_n = uvm_reset::sequence_start::type_id::create("m_pcie_sysrst_n");
    endfunction

    virtual task run_rq(int unsigned pcie, int unsigned dma);
        while (stop == 0) begin
            assert (dma_rq[pcie][dma].randomize());
            dma_rq[pcie][dma].start(p_sequencer.m_dma_rq[pcie][dma]);
        end
        rx_stop[pcie][dma] = 1;
    endtask

    //RUN RC
    virtual task run_rc(int unsigned pcie, int unsigned dma);
    endtask

    //RUN CQ
    virtual task run_cq(int unsigned pcie, int unsigned dma);
        //TX have its own RDY generator
        //forever begin
        //    assert(m_mfb_cq[pcie][dma].randomize()) else `uvm_fatal(p_sequencer.m_dma_cq[pcie][dma].get_full_name(), "\n\tCannot randomize sequence");;
        //    m_mfb_cq[pcie][dma].start(p_sequencer.m_dma_cq[pcie][dma]);
        //end
    endtask

    virtual task run_cc(int unsigned pcie, int unsigned dma);
        uvm_pcie::pcie_info#(8)   pcie_rc_info;

        uvm_config_db #(uvm_pcie::pcie_info#(8))::get(p_sequencer.m_dma_cc[pcie][dma], "", "pcie_info", pcie_rc_info);

        // TODO: DONT STOP IF THERE IS UNRESPONDED REQUEST
        //while (p_sequencer.m_pcie[pcie].info.rq_hdr.size() != 0 || (& rx_stop[pcie]) == 0) begin
        while (tx_stop == 0 || pcie_rc_info.request_num() != 0) begin
            assert(m_dma_cc[pcie][dma].randomize()) else `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize pcie sequence");
            m_dma_cc[pcie][dma].start(p_sequencer.m_dma_cc[pcie][dma]);
        end
        //forever begin
        //    assert(m_dma_cc[pcie][dma].randomize()) else `uvm_fatal(p_sequencer.m_dma_cc[pcie][dma].get_full_name(), "\n\tCannot randomize sequence");;
        //    m_dma_cc[pcie][dma].start(p_sequencer.m_dma_cc[pcie][dma]);
        //end
    endtask

    //RUN MI
    virtual task run_mi(int unsigned pcie);
        //while (stop == 0) begin
        forever begin
            assert(mi_seq[pcie].randomize()) else `uvm_fatal(p_sequencer.m_mi_sqr[pcie].get_full_name(), "\n\tCannot randomize sequence");
            mi_seq[pcie].start(p_sequencer.m_mi_sqr[pcie]);
        end
    endtask

    //RUN PCIE
    virtual task run_pcie_rc(int unsigned pcie);
        uvm_pcie::pcie_info#(8)   pcie_rc_info;

        uvm_config_db #(uvm_pcie::pcie_info#(8))::get(p_sequencer.m_pcie_rc[pcie], "", "pcie_info", pcie_rc_info);

        // TODO: DONT STOP IF THERE IS UNRESPONDED REQUEST
        //while (p_sequencer.m_pcie[pcie].info.rq_hdr.size() != 0 || (& rx_stop[pcie]) == 0) begin
        while (tx_stop == 0 || pcie_rc_info.request_num() != 0) begin
            assert(pcie_seq_rc[pcie].randomize()) else `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize pcie sequence");
            pcie_seq_rc[pcie].start(p_sequencer.m_pcie_rc[pcie]);
        end
    endtask

    virtual task run_pcie_cq(int unsigned pcie);
        #(200ns)
        while (stop == 0) begin
            assert(pcie_seq_cq[pcie].randomize()) else `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize pcie sequence");
            pcie_seq_cq[pcie].start(p_sequencer.m_pcie_cq[pcie]);
        end
    endtask

    task run_reset(uvm_reset::sequence_start m_reset, uvm_reset::sequencer m_reset_sqr);
        assert(m_reset.randomize());
        m_reset.start(m_reset_sqr);
    endtask

    task body();
        //Run RESET
        stop = 0;
        tx_stop = 0;

        fork
            run_reset(m_dma_reset, p_sequencer.m_dma_reset);
            run_reset(m_mi_reset, p_sequencer.m_mi_reset);
            run_reset(m_pcie_sysrst_n, p_sequencer.m_pcie_sysrst_n);
        join_none

        #(1us);

        for (int unsigned pcie = 0; pcie < PCIE_ENDPOINTS; pcie++) begin
            fork
                automatic int unsigned index_pcie = pcie;
                for (int dma = 0; dma < DMA_PORTS; dma++) begin
                    fork
                        automatic int unsigned index_dma = dma;
                        run_rq(index_pcie, index_dma);
                        //run_rc(index_pcie, index_dma);
                        run_cq(index_pcie, index_dma);
                        //run_cc(index_pcie, index_dma);
                    join_none
                end
                run_pcie_cq(index_pcie);
                run_pcie_rc(index_pcie);
                run_mi(index_pcie);
            join_none
        end

        //#(50ms);
        #(1ms);
        stop = 1;
        for (int unsigned it = 0; it < PCIE_ENDPOINTS; it++) begin
            wait (rx_stop[it] == 0);
        end
    endtask
endclass


