//-- test.sv: Verification test
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    uvm_ptc::env #(DMA_MFB_UP_REGIONS, MFB_UP_REGIONS, MFB_UP_REG_SIZE,
                   MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH, MFB_DOWN_REGIONS,
                   DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE,
                   MFB_DOWN_ITEM_WIDTH, PCIE_UPHDR_WIDTH, PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, DMA_MVB_UP_ITEMS,
                   DMA_MVB_DOWN_ITEMS, RQ_TUSER_WIDTH, RC_TUSER_WIDTH, RQ_TDATA_WIDTH, RQ_TDATA_WIDTH, META_WIDTH, DMA_PORTS, ENDPOINT_TYPE, RCB_SIZE, CLK_PERIOD, DEVICE) m_env;

    int unsigned timeout;
    logic [DMA_PORTS-1 : 0] event_vseq;

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_ptc::env #(DMA_MFB_UP_REGIONS, MFB_UP_REGIONS, MFB_UP_REG_SIZE,
                               MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH, MFB_DOWN_REGIONS,
                               DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE,
                               MFB_DOWN_ITEM_WIDTH, PCIE_UPHDR_WIDTH, PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, DMA_MVB_UP_ITEMS,
                               DMA_MVB_DOWN_ITEMS, RQ_TUSER_WIDTH, RC_TUSER_WIDTH, RQ_TDATA_WIDTH, RQ_TDATA_WIDTH, META_WIDTH, DMA_PORTS, ENDPOINT_TYPE, RCB_SIZE, CLK_PERIOD, DEVICE)::type_id::create("m_env", this);
    endfunction

    virtual task rq_seq;
        uvm_mfb::sequence_lib_tx#(MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, 32, 0) rq_mfb_lib;
        uvm_axi::sequence_lib_tx #(RQ_TDATA_WIDTH, RQ_TUSER_WIDTH, MFB_UP_REGIONS) rq_axi_lib;
        rq_mfb_lib = uvm_mfb::sequence_lib_tx#(MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, 32, 0)::type_id::create("mfb_eth_rq_seq", this);
        rq_axi_lib = uvm_axi::sequence_lib_tx #(RQ_TDATA_WIDTH, RQ_TUSER_WIDTH, MFB_UP_REGIONS)::type_id::create("axi_rq_seq", this);

        rq_mfb_lib.init_sequence();
        rq_mfb_lib.cfg = new();
        rq_mfb_lib.cfg.probability_set(RQ_MFB_DST_RDY_PROB_MIN, RQ_MFB_DST_RDY_PROB_MAX);
        rq_mfb_lib.min_random_count = 60;
        rq_mfb_lib.max_random_count = 80;

        rq_axi_lib.init_sequence();
        rq_axi_lib.cfg = new();
        rq_axi_lib.cfg.probability_set(RQ_MFB_DST_RDY_PROB_MIN, RQ_MFB_DST_RDY_PROB_MAX);
        rq_axi_lib.min_random_count = 60;
        rq_axi_lib.max_random_count = 80;

        forever begin
            if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
                rq_mfb_lib.start(m_env.m_env_rq_mfb.m_sequencer);
            end else
                rq_axi_lib.start(m_env.m_env_rq_axi.m_sequencer);
        end
    endtask

    virtual task down_seq(int unsigned index);
        uvm_mfb::sequence_lib_tx#(DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, META_WIDTH) down_seq;
        down_seq = uvm_mfb::sequence_lib_tx#(DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, META_WIDTH)::type_id::create($sformatf("mfb_eth_down_seq%0d", index));
        down_seq.init_sequence();
        down_seq.cfg = new();
        down_seq.cfg.probability_set(DOWN_MFB_DST_RDY_PROB_MIN, DOWN_MFB_DST_RDY_PROB_MAX);
        down_seq.min_random_count = 60;
        down_seq.max_random_count = 80;

        forever begin
            down_seq.start(m_env.m_env_down_mfb[index].m_sequencer);
        end
    endtask

    virtual task down_mvb_seq(int unsigned index);
        uvm_mvb::sequence_lib_tx#(DMA_MVB_DOWN_ITEMS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH) down_mvb_seq;
        down_mvb_seq = uvm_mvb::sequence_lib_tx#(DMA_MVB_DOWN_ITEMS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)::type_id::create($sformatf("mvb_eth_down_seq%0d", index));
        down_mvb_seq.init_sequence();
        down_mvb_seq.cfg = new();
        down_mvb_seq.cfg.probability_set(DOWN_MVB_DST_RDY_PROB_MIN, DOWN_MVB_DST_RDY_PROB_MAX);
        down_mvb_seq.min_random_count = 60;
        down_mvb_seq.max_random_count = 80;

        forever begin
            down_mvb_seq.start(m_env.m_env_down_mvb[index].m_mvb_agent.m_sequencer);
        end
    endtask

    task run_seq(int unsigned index);
        virt_seq #(MRRS, MIN_READ_REQ_SIZE, MPS, MIN_WRITE_REQ_SIZE) m_vseq;
        m_vseq = virt_seq #(MRRS, MIN_READ_REQ_SIZE, MPS, MIN_WRITE_REQ_SIZE)::type_id::create($sformatf("m_vseq%0d", index));
        m_vseq.randomize();
        m_vseq.start(m_env.m_env_up[index].m_sequencer);
        event_vseq[index] = 1'b0;

    endtask

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    virtual task run_phase(uvm_phase phase);

        event_vseq = '1;

        phase.raise_objection(this);
        #(100ns);

        fork
            rq_seq();
        join_none

        for (int i = 0; i < DMA_PORTS; i++) begin
            fork
                automatic int index = i;
                down_seq(index);
            join_none
        end

        for (int i = 0; i < DMA_PORTS; i++) begin
            fork
                automatic int index = i;
                down_mvb_seq(index);
            join_none
        end

        for (int i = 0; i < DMA_PORTS; i++) begin
            fork
                automatic int index = i;
                run_seq(index);
            join_none
        end

        for (int unsigned it = 0; it < DMA_PORTS; it++) begin
            wait(event_vseq[it] == 1'b0);
        end

        timeout = 1;
        fork
            test_wait_timeout(1000);
            test_wait_result();
        join_any;

        phase.drop_objection(this);

    endtask

    task test_wait_timeout(int unsigned time_length);
        #(time_length*1us);
    endtask

    task test_wait_result();
        do begin
            #(600ns);
        end while (m_env.sc.used() != 0);
        timeout = 0;
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
        if (timeout) begin
            `uvm_error(this.get_full_name(), "\n\t===================================================\n\tTIMEOUT SOME PACKET STUCK IN DESIGN\n\t===================================================\n\n");
        end
    endfunction

endclass
