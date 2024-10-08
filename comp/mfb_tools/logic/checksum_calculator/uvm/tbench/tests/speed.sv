// test.sv: Verification test
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class mfb_rx_speed#(MFB_REGIONS, MFB_REGION_SIZE, MFB_ITEM_WIDTH, MFB_BLOCK_SIZE, META_WIDTH) extends uvm_logic_vector_array_mfb::sequence_lib_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_ITEM_WIDTH, MFB_BLOCK_SIZE, META_WIDTH);
  `uvm_object_param_utils(test::mfb_rx_speed#(MFB_REGIONS, MFB_REGION_SIZE, MFB_ITEM_WIDTH, MFB_BLOCK_SIZE, META_WIDTH))
  `uvm_sequence_library_utils(test::mfb_rx_speed#(MFB_REGIONS, MFB_REGION_SIZE, MFB_ITEM_WIDTH, MFB_BLOCK_SIZE, META_WIDTH))

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
        this.add_sequence(uvm_logic_vector_array_mfb::sequence_full_speed_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_ITEM_WIDTH, MFB_BLOCK_SIZE, META_WIDTH)::get_type());
    endfunction
endclass

class mvb_tx_speed#(MFB_REGIONS, MVB_DATA_WIDTH) extends uvm_mvb::sequence_lib_tx#(MFB_REGIONS, MVB_DATA_WIDTH);
  `uvm_object_param_utils(test::mvb_tx_speed#(MFB_REGIONS, MVB_DATA_WIDTH))
  `uvm_sequence_library_utils(test::mvb_tx_speed#(MFB_REGIONS, MVB_DATA_WIDTH))

    function new(string name = "mvb_tx_speed");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(uvm_mvb::config_sequence param_cfg = null);
        if (param_cfg == null) begin
            this.cfg = new();
        end else begin
            this.cfg = param_cfg;
        end
        this.add_sequence(uvm_mvb::sequence_full_speed_tx #(MFB_REGIONS, MVB_DATA_WIDTH)::get_type());
    endfunction
endclass

class speed extends uvm_test;
     typedef uvm_component_registry#(test::speed, "test::speed") type_id;

    // declare the Environment reference variable
    uvm_checksum_calculator::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH, VERBOSITY, MFB_META_WIDTH) m_env;
    test::mvb_tx_speed#(MFB_REGIONS, MVB_DATA_WIDTH+1+MFB_META_WIDTH)                                                                                  mvb_tx_speed;
    uvm_reset::sequence_start                                                                                                           m_reset;
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
        uvm_logic_vector_array_mfb::sequence_lib_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH)::type_id::set_inst_override(mfb_rx_speed#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH)::get_type(),
        {this.get_full_name(), ".m_env.m_env_rx.*"});
        // Initializing the reference to the environment
        m_env = uvm_checksum_calculator::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH, VERBOSITY, MFB_META_WIDTH)::type_id::create("m_env", this);
    endfunction

    virtual task tx_mvb_seq();
        forever begin
            mvb_tx_speed.randomize();
            mvb_tx_speed.start(m_env.m_env_tx_mvb.m_sequencer);
        end
    endtask

    virtual task run_reset();
        m_reset.randomize();
        m_reset.start(m_env.m_reset.m_sequencer);
    endtask

    virtual function void init();

        m_reset      = uvm_reset::sequence_start::type_id::create("m_reset_seq");
        mvb_tx_speed = test::mvb_tx_speed#(MFB_REGIONS, MVB_DATA_WIDTH+1+MFB_META_WIDTH)::type_id::create("mvb_tx_speed");

        mvb_tx_speed.init_sequence();
        mvb_tx_speed.min_random_count = 100;
        mvb_tx_speed.max_random_count = 200;

    endfunction


    // ------------------------------------------------------------------------
    // Create environment and Run sequences on their sequencers
    virtual task run_phase(uvm_phase phase);
        virt_sequence#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) m_vseq;

        phase.raise_objection(this);

        m_vseq = virt_sequence#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH)::type_id::create("m_vseq");

        init();

        fork
            run_reset();
        join_none

        #(100ns);

        //RUN VSEQ and MVB TX SEQUENCE
        fork
            tx_mvb_seq();
        join_none

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
