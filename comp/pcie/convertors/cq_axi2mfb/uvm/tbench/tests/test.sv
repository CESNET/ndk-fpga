//-- test.sv: Verification test
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    bit timeout;
    uvm_cq_mfb2axi::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, STRADDLING, DEVICE) m_env;

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_cq_mfb2axi::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, STRADDLING, DEVICE)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    virtual task run_phase(uvm_phase phase);
        time time_start;
        virt_sequence m_vseq;

        phase.raise_objection(this, "Start of rx sequence");

        m_vseq = virt_sequence::type_id::create("m_vseq");
        assert(m_vseq.randomize());
        m_vseq.start(m_env.m_sequencer);

        //STOP TEST
        time_start = $time;
        while((time_start + 10ms) > $time && m_env.used()) begin
            #(600ns);
        end
        phase.drop_objection(this, "End of rx sequence");
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass
