// sequence.sv : virtual sequence
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_base #(
    RC_MFB_REGIONS,
    RC_MFB_REGION_SIZE,
    RC_MFB_BLOCK_SIZE,
    RC_MFB_META_W,
    
    CQ_MFB_REGIONS,
    CQ_MFB_REGION_SIZE,
    CQ_MFB_BLOCK_SIZE,
    CQ_MFB_META_W,
        
    RQ_MFB_META_W,

    CC_MFB_REGIONS,
    CC_MFB_REGION_SIZE,
    CC_MFB_BLOCK_SIZE,
    CC_MFB_META_W,
    
    ITEM_WIDTH,
    DMA_PORTS, PCIE_CONS, PCIE_ENDPOINTS) extends uvm_sequence; 
    `uvm_object_param_utils(uvm_pcie_top::sequence_base#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_META_W, CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE,  CQ_MFB_BLOCK_SIZE, CQ_MFB_META_W,
                                                         RQ_MFB_META_W,  CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_META_W, ITEM_WIDTH, DMA_PORTS, PCIE_CONS, PCIE_ENDPOINTS))

     `uvm_declare_p_sequencer(uvm_pcie_top::sequencer#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_META_W,
                                                       CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_META_W,
                                                       ITEM_WIDTH, RQ_MFB_META_W, CC_MFB_META_W, DMA_PORTS, PCIE_ENDPOINTS))

    protected int unsigned stop;
    //RQ
    uvm_pcie_top::sequence_dma_rq#(DMA_PORTS) dma_rq[PCIE_ENDPOINTS][DMA_PORTS];
    //RC
    uvm_sequence #(uvm_mfb::sequence_item #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, ITEM_WIDTH, RC_MFB_META_W)) m_mfb_rc[PCIE_ENDPOINTS][DMA_PORTS];
    uvm_sequence #(uvm_mvb::sequence_item #(RC_MFB_REGIONS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH))                               m_mvb_rc[PCIE_ENDPOINTS][DMA_PORTS];
    //CQ
    uvm_sequence #(uvm_mfb::sequence_item #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, CQ_MFB_META_W)) m_mfb_cq[PCIE_ENDPOINTS][DMA_PORTS];
    //CC

    //MI
    uvm_pcie_top::mi_cc_sequence #(32, 32) mi_seq[PCIE_ENDPOINTS];

    //PCIE
    uvm_pcie::sequence_base pcie_seq[PCIE_ENDPOINTS];

    // Start reset sequence
    uvm_reset::sequence_start m_dma_reset;
    uvm_reset::sequence_start m_mi_reset;
    uvm_reset::sequence_start m_pcie_sysrst_n;

    //STOP SEQUENCE
    //sequences_cfg_sync#(int unsigned NUM) sync;

    function new(string name = "sequence_simple_rx_base");
        super.new(name);
    endfunction

    virtual function void init(
        uvm_pcie_top::sequencer#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_META_W,
                                 CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_META_W,
                                 ITEM_WIDTH, RQ_MFB_META_W, CC_MFB_META_W, DMA_PORTS, PCIE_ENDPOINTS) p_sequencer);

        for (int unsigned pcie = 0; pcie < PCIE_ENDPOINTS; pcie++) begin
             string pcie_string;
             pcie_string.itoa(pcie);

             for (int dma = 0; dma < DMA_PORTS; dma++) begin
                string dma_string = {pcie_string, $sformatf("_%0d", dma)};
                uvm_mfb::sequence_lib_tx  #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, ITEM_WIDTH, RC_MFB_META_W)              m_mfb_rc_lib;
                uvm_mvb::sequence_lib_tx #(RC_MFB_REGIONS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)                                             m_mvb_rc_lib;
                uvm_mfb::sequence_lib_tx  #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, CQ_MFB_META_W)              m_mfb_cq_lib;

                //RQ
                dma_rq[pcie][dma] = uvm_pcie_top::sequence_dma_rq#(DMA_PORTS)::type_id::create("dma_rq", p_sequencer.m_dma_rq[pcie][dma]);

                //RC
                m_mfb_rc_lib  = uvm_mfb::sequence_lib_tx#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, ITEM_WIDTH, RC_MFB_META_W)::type_id::create({"m_mfb_rc_lib_", dma_string}, p_sequencer.m_dma_rc_mfb[pcie][dma]);
                m_mfb_rc_lib.init_sequence();
                m_mfb_rc_lib.min_random_count = 100;
                m_mfb_rc_lib.max_random_count = 200;
                m_mfb_rc[pcie][dma] = m_mfb_rc_lib;

                m_mvb_rc_lib  = uvm_mvb::sequence_lib_tx#(RC_MFB_REGIONS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)::type_id::create({"m_mvb_rc_lib_", dma_string}, p_sequencer.m_dma_rc_mvb[pcie][dma]);
                m_mvb_rc_lib.init_sequence();
                m_mvb_rc_lib.min_random_count = 100;
                m_mvb_rc_lib.max_random_count = 200;
                m_mvb_rc[pcie][dma] = m_mvb_rc_lib;

                //CQ
                m_mfb_cq_lib  = uvm_mfb::sequence_lib_tx#(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, CQ_MFB_META_W)::type_id::create({"m_mfb_cq_lib_", dma_string}, p_sequencer.m_dma_cq[pcie][dma]);
                m_mfb_cq_lib.init_sequence();
                m_mfb_cq_lib.min_random_count = 100;
                m_mfb_cq_lib.max_random_count = 200;
                m_mfb_cq[pcie][dma] = m_mfb_cq_lib;
             end

             //MI interface
             mi_seq[pcie] = uvm_pcie_top::mi_cc_sequence #(32, 32)::type_id::create({"mi_seq_", pcie_string}, p_sequencer.m_mi_sqr[pcie]);

             //PCIE
             pcie_seq[pcie] = new(); //uvm_pcie::sequence_base::type_id::create({"pcie_seq_", pcie_string}, p_sequencer.m_pcie[pcie]);
        end

        m_dma_reset     = uvm_reset::sequence_start::type_id::create("m_dma_reset");
        m_mi_reset      = uvm_reset::sequence_start::type_id::create("m_mi_reset");
        m_pcie_sysrst_n = uvm_reset::sequence_start::type_id::create("m_pcie_sysrst_n");
    endfunction

    virtual task run_rq(int unsigned pcie, int unsigned dma);
        const int unsigned dma_unitid_const = (DMA_PORTS*pcie + dma);

        while (stop == 0) begin
            assert (dma_rq[pcie][dma].randomize() with {dma_rq[pcie][dma].unit_id ==  dma_unitid_const;});
            dma_rq[pcie][dma].start(p_sequencer.m_dma_rq[pcie][dma]);
        end
    endtask

    //RUN RC
    virtual task run_rc(int unsigned pcie, int unsigned dma);
        fork
            forever begin
                assert(m_mfb_rc[pcie][dma].randomize());
                m_mfb_rc[pcie][dma].start(p_sequencer.m_dma_rc_mfb[pcie][dma]);
            end

            forever begin
                assert(m_mvb_rc[pcie][dma].randomize());
                m_mvb_rc[pcie][dma].start(p_sequencer.m_dma_rc_mvb[pcie][dma]);
            end
        join
    endtask

    //RUN CQ
    virtual task run_cq(int unsigned pcie, int unsigned dma);
        forever begin
            assert(m_mfb_cq[pcie][dma].randomize()) else `uvm_fatal(p_sequencer.m_dma_cq[pcie][dma].get_full_name(), "\n\tCannot randomize sequence");;
            m_mfb_cq[pcie][dma].start(p_sequencer.m_dma_cq[pcie][dma]);
        end
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
    virtual task run_pcie(int unsigned pcie);

        while (p_sequencer.m_pcie[pcie].info.rq_hdr.size() != 0 || stop == 0) begin
            assert(pcie_seq[pcie].randomize()) else `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize pcie sequence");
            pcie_seq[pcie].response_only = (stop == 1);
            pcie_seq[pcie].start(p_sequencer.m_pcie[pcie]);
        end
    endtask



    task run_reset(uvm_reset::sequence_start m_reset, uvm_reset::sequencer m_reset_sqr);
        assert(m_reset.randomize());
        m_reset.start(m_reset_sqr);
    endtask

    task body();
        //Run RESET
        stop = 0;

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
                        run_rc(index_pcie, index_dma);
                        run_cq(index_pcie, index_dma);
                    join_none
                end
                run_pcie(index_pcie); 
                run_mi(index_pcie);
            join_none
        end

        //#(50ms);
        #(1ms);
        stop = 1;
        //wait();
    endtask
endclass

