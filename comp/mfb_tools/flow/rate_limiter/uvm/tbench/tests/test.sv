// test.sv: Verification test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Tomas Hak <xhakto01@vut.cz>

// SPDX-License-Identifier: BSD-3-Clause

class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test)

    uvm_rate_limiter::env#(MI_DATA_WIDTH, MI_ADDR_WIDTH, MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, INTERVAL_COUNT, SHAPING_TYPE, CLK_PERIOD) m_env;

    int unsigned timeout;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array_mfb::sequence_lib_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::set_inst_override(test::sequence_lib_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::get_type(), {this.get_full_name(), ".m_env.m_env_rx.*"});
        m_env = uvm_rate_limiter::env#(MI_DATA_WIDTH, MI_ADDR_WIDTH, MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, INTERVAL_COUNT, SHAPING_TYPE, CLK_PERIOD)::type_id::create("m_env", this);
    endfunction

    task run_phase(uvm_phase phase);
        test::virt_seq#(SECTION_LENGTH, INTERVAL_LENGTH, INTERVAL_COUNT, SHAPING_TYPE, OUTPUT_SPEED, MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) m_vseq;
        m_vseq = test::virt_seq#(SECTION_LENGTH, INTERVAL_LENGTH, INTERVAL_COUNT, SHAPING_TYPE, OUTPUT_SPEED, MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::create("m_vseq");
        m_vseq.regmodel_set(m_env.m_regmodel.m_regmodel);
        m_vseq.init();

        phase.raise_objection(this);

        fork
            begin
                void'(m_vseq.randomize());
                m_vseq.start(m_env.m_sequencer);
            end
        join_none

        timeout = 1;
        #(INTERVAL_COUNT*INTERVAL_LENGTH*SECTION_LENGTH*2*CLK_PERIOD);

        fork
            test_wait_timeout(1000);
            test_wait_result();
        join_any

        phase.drop_objection(this);
    endtask

    task test_wait_timeout(int unsigned time_length);
        #(time_length*1ms);
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
