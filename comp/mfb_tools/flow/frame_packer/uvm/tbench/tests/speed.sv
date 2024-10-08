// speed.sv: Verification test
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:   David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class virt_seq_full_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_CHANNELS, PKT_MTU) extends virt_sequence #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_CHANNELS, PKT_MTU);
    `uvm_object_param_utils (test::virt_seq_full_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_CHANNELS, PKT_MTU))
    uvm_framepacker::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, SPACE_SIZE_MIN_RX, SPACE_SIZE_MAX_RX, SPACE_SIZE_MIN_TX, SPACE_SIZE_MAX_TX, RX_CHANNELS, USR_RX_PKT_SIZE_MAX, HDR_META_WIDTH) m_env;

    function new (string name = "virt_seq_full_speed");
        super.new(name);
    endfunction

    virtual function void init(int unsigned frame_size_min, int unsigned frame_size_max);
        super.init(frame_size_min, frame_size_max);
        m_mfb_rdy_seq = uvm_mfb::sequence_full_speed_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create("m_mfb_rdy_seq");
        m_mvb_rdy_seq = uvm_mvb::sequence_full_speed_tx #(MFB_REGIONS, $clog2(RX_CHANNELS) + $clog2(PKT_MTU+1) + HDR_META_WIDTH + 1)::type_id::create("m_mvb_rdy_seq");
    endfunction

endclass

class mvb_rx_speed#(MFB_REGIONS, MVB_ITEM_WIDTH) extends uvm_logic_vector_mvb::sequence_lib_rx#(MFB_REGIONS, MVB_ITEM_WIDTH);
  `uvm_object_param_utils(test::mvb_rx_speed#(MFB_REGIONS, MVB_ITEM_WIDTH))
  `uvm_sequence_library_utils(test::mvb_rx_speed#(MFB_REGIONS, MVB_ITEM_WIDTH))

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
        this.add_sequence(uvm_logic_vector_mvb::sequence_full_speed_rx #(MFB_REGIONS, MVB_ITEM_WIDTH)::get_type());
    endfunction
endclass

class speed extends uvm_test;
     typedef uvm_component_registry #(test::speed, "test::speed") type_id;

    // declare the Environment reference variable
    uvm_framepacker::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, SPACE_SIZE_MIN_RX, SPACE_SIZE_MAX_RX, SPACE_SIZE_MIN_TX, SPACE_SIZE_MAX_TX, RX_CHANNELS, USR_RX_PKT_SIZE_MAX, HDR_META_WIDTH) m_env;
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
        uvm_logic_vector_array_mfb::sequence_lib_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::set_inst_override(uvm_logic_vector_array_mfb::sequence_lib_rx_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::get_type(),
        {this.get_full_name(), ".m_env.mfb_rx_env.*"});
        uvm_logic_vector_mvb::sequence_lib_rx#(MFB_REGIONS, $clog2(RX_CHANNELS) + $clog2(USR_RX_PKT_SIZE_MAX+1))::type_id::set_inst_override(mvb_rx_speed#(MFB_REGIONS, $clog2(RX_CHANNELS) + $clog2(USR_RX_PKT_SIZE_MAX+1))::get_type(),
        {this.get_full_name(), ".m_env.mvb_rx_env.*"});

        // Initializing the reference to the environment
        m_env = uvm_framepacker::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, SPACE_SIZE_MIN_RX, SPACE_SIZE_MAX_RX, SPACE_SIZE_MIN_TX, SPACE_SIZE_MAX_TX, RX_CHANNELS, USR_RX_PKT_SIZE_MAX, HDR_META_WIDTH)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences on their sequencers
    virtual task run_phase(uvm_phase phase);
        virt_seq_full_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_CHANNELS, USR_RX_PKT_SIZE_MAX) m_vseq;
        m_vseq = virt_seq_full_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_CHANNELS, USR_RX_PKT_SIZE_MAX)::type_id::create("m_vseq");

        phase.raise_objection(this);

        m_vseq.init(FRAME_SIZE_MIN, FRAME_SIZE_MAX);

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
            #(600ns);
        end while (m_env.m_scoreboard.used() != 0);
        timeout = 0;
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
        if (timeout) begin
            `uvm_error(this.get_full_name(), "\n\t===================================================\n\tTIMEOUT SOME PACKET STUCK IN DESIGN\n\t===================================================\n\n");
        end
    endfunction
endclass
