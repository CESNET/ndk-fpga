//-- test.sv: Verification test
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class virt_seq_slow_dma_down#(MRRS, MIN_READ_REQ_SIZE, MPS, MIN_WRITE_REQ_SIZE) extends virt_seq#(MRRS, MIN_READ_REQ_SIZE, MPS, MIN_WRITE_REQ_SIZE);

    `uvm_object_param_utils(test::virt_seq_slow_dma_down#(MRRS, MIN_READ_REQ_SIZE, MPS, MIN_WRITE_REQ_SIZE))

    `uvm_declare_p_sequencer(uvm_dma_up::sequencer)

    function new (string name = "virt_seq_slow_dma_down");
        super.new(name);
    endfunction

    virtual function void init();
        super.init();
        m_info = uvm_ptc_info::sequence_simple_read#(MRRS, MIN_READ_REQ_SIZE)::type_id::create("m_info");
    endfunction
endclass


class sequence_stop_var_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, TR_MIN, TR_MAX) extends uvm_mfb::sequence_stop_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `uvm_object_param_utils(test::sequence_stop_var_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, TR_MIN, TR_MAX))

    // ------------------------------------------------------------------------
    // Variables
    uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) req;

    int unsigned max_transaction_count = TR_MAX;
    int unsigned min_transaction_count = TR_MIN;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[min_transaction_count: max_transaction_count]};}
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_stop_var_tx");
        super.new(name);
    endfunction

    task send_frame();
        start_item(req);
        void'(req.randomize() with {dst_rdy == 1'b0;});
        finish_item(req);
        get_response(rsp);
    endtask


    // ------------------------------------------------------------------------
    // Generates transactions
    task body;
        // Generate transaction_count transactions
        req = uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("req");
        repeat(transaction_count) begin
            // Create a request for sequence item
            send_frame();
        end
    endtask
endclass

class sequence_mvb_stop_var_tx #(ITEMS, ITEM_WIDTH, TR_MIN, TR_MAX) extends uvm_mvb::sequence_stop_tx #(ITEMS, ITEM_WIDTH);
    `uvm_object_param_utils(test::sequence_mvb_stop_var_tx #(ITEMS, ITEM_WIDTH, TR_MIN, TR_MAX))

    // ------------------------------------------------------------------------
    // Variables
    uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH) req;

    int unsigned max_transaction_count = TR_MAX;
    int unsigned min_transaction_count = TR_MIN;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[min_transaction_count: max_transaction_count]};}
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_mvb_stop_var_tx");
        super.new(name);
    endfunction

    task send_frame();
        start_item(req);
        void'(req.randomize() with {dst_rdy == 1'b0;});
        finish_item(req);
        get_response(rsp);
    endtask


    // ------------------------------------------------------------------------
    // Generates transactions
    task body;
        // Generate transaction_count transactions
        req = uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH)::type_id::create("req");
        repeat(transaction_count) begin
            // Create a request for sequence item
            send_frame();
        end
    endtask
endclass

class mfb_tx_slow #(MFB_REGIONS, MFB_REGION_SIZE, MFB_ITEM_WIDTH, MFB_BLOCK_SIZE, META_WIDTH, TR_MIN, TR_MAX) extends uvm_mfb::sequence_lib_tx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_ITEM_WIDTH, MFB_BLOCK_SIZE, META_WIDTH);
  `uvm_object_param_utils(test::mfb_tx_slow#(MFB_REGIONS, MFB_REGION_SIZE, MFB_ITEM_WIDTH, MFB_BLOCK_SIZE, META_WIDTH, TR_MIN, TR_MAX))
  `uvm_sequence_library_utils(test::mfb_tx_slow#(MFB_REGIONS, MFB_REGION_SIZE, MFB_ITEM_WIDTH, MFB_BLOCK_SIZE, META_WIDTH, TR_MIN, TR_MAX))

    function new(string name = "mfb_tx_slow");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(uvm_mfb::config_sequence param_cfg = null);
        if (param_cfg == null) begin
            this.cfg = new();
        end else begin
            this.cfg = param_cfg;
        end
        this.add_sequence(uvm_mfb::sequence_simple_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
        this.add_sequence(test::sequence_stop_var_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, TR_MIN, TR_MAX)::get_type());
    endfunction
endclass

class mvb_tx_slow #(MVB_ITEMS, MVB_DATA_WIDTH, TR_MIN, TR_MAX) extends uvm_mvb::sequence_lib_tx#(MVB_ITEMS, MVB_DATA_WIDTH);
  `uvm_object_param_utils(test::mvb_tx_slow#(MVB_ITEMS, MVB_DATA_WIDTH, TR_MIN, TR_MAX))
  `uvm_sequence_library_utils(test::mvb_tx_slow#(MVB_ITEMS, MVB_DATA_WIDTH, TR_MIN, TR_MAX))

    function new(string name = "mvb_tx_slow");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(uvm_mvb::config_sequence param_cfg = null);
        if (param_cfg == null) begin
            this.cfg = new();
        end else begin
            this.cfg = param_cfg;
        end
        this.add_sequence(test::sequence_mvb_stop_var_tx#(ITEMS, ITEM_WIDTH, TR_MIN, TR_MAX)::get_type());
        this.add_sequence(uvm_mvb::sequence_simple_tx#(ITEMS, ITEM_WIDTH)::get_type());
    endfunction
endclass

class slow_dma_down_test extends uvm_test;
    `uvm_component_utils(test::slow_dma_down_test);

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
        rq_mfb_lib.min_random_count = 60;
        rq_mfb_lib.max_random_count = 80;

        rq_axi_lib.init_sequence();
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
        test::mfb_tx_slow#(DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, META_WIDTH, TR_MIN, TR_MAX) down_seq;
        down_seq = test::mfb_tx_slow#(DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, META_WIDTH, TR_MIN, TR_MAX)::type_id::create($sformatf("mfb_tx_slow%0d", index));
        down_seq.init_sequence();
        down_seq.min_random_count = 60;
        down_seq.max_random_count = 80;

        forever begin
            down_seq.start(m_env.m_env_down_mfb[index].m_sequencer);
        end
    endtask

    virtual task down_mvb_seq(int unsigned index);
        test::mvb_tx_slow#(DMA_MVB_DOWN_ITEMS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH, TR_MIN, TR_MAX) down_mvb_seq;
        down_mvb_seq = test::mvb_tx_slow#(DMA_MVB_DOWN_ITEMS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH, TR_MIN, TR_MAX)::type_id::create($sformatf("mvb_tx_slow%0d", index));
        down_mvb_seq.init_sequence();
        down_mvb_seq.min_random_count = 60;
        down_mvb_seq.max_random_count = 80;

        forever begin
            down_mvb_seq.start(m_env.m_env_down_mvb[index].m_mvb_agent.m_sequencer);
        end
    endtask

    task run_seq(int unsigned index);
        virt_seq_slow_dma_down #(MRRS, MIN_READ_REQ_SIZE, MPS, MIN_WRITE_REQ_SIZE) m_vseq;
        m_vseq = virt_seq_slow_dma_down #(MRRS, MIN_READ_REQ_SIZE, MPS, MIN_WRITE_REQ_SIZE)::type_id::create($sformatf("m_vseq%0d", index));
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
