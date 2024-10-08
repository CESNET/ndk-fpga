// test.sv: Verification test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class virt_seq_full_speed#(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, FRAME_SIZE_MIN, FRAME_SIZE_MAX) extends virt_sequence #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, FRAME_SIZE_MIN, FRAME_SIZE_MAX);
    `uvm_object_param_utils(test::virt_seq_full_speed#(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, FRAME_SIZE_MIN, FRAME_SIZE_MAX))
    `uvm_declare_p_sequencer(uvm_mfb_crossbarx_stream2::virt_sequencer#(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W))

    function new (string name = "virt_seq_full_speed");
        super.new(name);
    endfunction

    virtual function void init(uvm_phase phase);
        super.init(phase);
        m_mfb_rdy_seq = uvm_mfb::sequence_full_speed_tx #(TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, USERMETA_W)::type_id::create("m_mfb_rdy_seq");
        m_mvb_rdy_seq = uvm_mvb::sequence_full_speed_tx #(TX_MFB_REGIONS, USERMETA_W)::type_id::create("m_mvb_rdy_seq");
    endfunction
endclass

class mvb_rx_speed#(RX_MFB_REGIONS, RX_MVB_ITEM_W) extends uvm_logic_vector_mvb::sequence_lib_rx#(RX_MFB_REGIONS, RX_MVB_ITEM_W);
  `uvm_object_param_utils(test::mvb_rx_speed#(RX_MFB_REGIONS, RX_MVB_ITEM_W))
  `uvm_sequence_library_utils(test::mvb_rx_speed#(RX_MFB_REGIONS, RX_MVB_ITEM_W))

    function new(string name = "mvb_rx_speed");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(uvm_logic_vector_mvb::config_sequence param_cfg = null);
        if (param_cfg == null) begin
            this.cfg = new();
        end else begin
            this.cfg = param_cfg;
        end
        this.add_sequence(uvm_logic_vector_mvb::sequence_full_speed_rx #(RX_MFB_REGIONS, RX_MVB_ITEM_W)::get_type());
    endfunction
endclass

class mfb_rx_speed#(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, USERMETA_W) extends uvm_logic_vector_array_mfb::sequence_lib_rx#(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, USERMETA_W);
  `uvm_object_param_utils(test::mfb_rx_speed#(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, USERMETA_W))
  `uvm_sequence_library_utils(test::mfb_rx_speed#(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, USERMETA_W))

    function new(string name = "mfb_rx_speed");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(uvm_logic_vector_array_mfb::config_sequence param_cfg = null);
        if (param_cfg == null) begin
            this.cfg = new();
        end else begin
            this.cfg = param_cfg;
        end
        this.add_sequence(uvm_logic_vector_array_mfb::sequence_full_speed_rx #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, USERMETA_W)::get_type());
    endfunction
endclass

class speed extends uvm_test;
     typedef uvm_component_registry#(test::speed, "test::speed") type_id;

    // declare the Environment reference variable
    uvm_mfb_crossbarx_stream2::env #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, MOD_W) m_env;
    int unsigned timeout;

    // ------------------------------------------------------------------------
    // Functions
    // Constrctor of the test object
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    static function type_id get_type();
        return type_id::get();
    endfunction

    function string get_type_name();
        return get_type().get_type_name();
    endfunction

    // Build phase function, e.g. the creation of test's internal objects
    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array_mfb::sequence_lib_rx#(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, USERMETA_W)::type_id::set_inst_override(mfb_rx_speed#(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, USERMETA_W)::get_type(),
        {this.get_full_name(), ".m_env.m_env_rx.*"});
        uvm_logic_vector_mvb::sequence_lib_rx#(RX_MFB_REGIONS, RX_MVB_ITEM_W)::type_id::set_inst_override(mvb_rx_speed#(RX_MFB_REGIONS, RX_MVB_ITEM_W)::get_type(),
        {this.get_full_name(), ".m_env.m_env_rx_mvb.*"});

        // Initializing the reference to the environment
        m_env = uvm_mfb_crossbarx_stream2::env #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, MOD_W)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences on their sequencers
    virtual task run_phase(uvm_phase phase);
        virt_seq_full_speed #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, FRAME_SIZE_MIN, FRAME_SIZE_MAX) m_vseq;
        m_vseq = virt_seq_full_speed #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, FRAME_SIZE_MIN, FRAME_SIZE_MAX)::type_id::create("m_vseq");

        phase.raise_objection(this);

        m_vseq.init(phase);

        //RUN MFB RX SEQUENCE
        m_vseq.randomize();
        m_vseq.start(m_env.vscr);

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
            #(100us);
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
