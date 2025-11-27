//-- sequence.sv
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequence_base extends uvm_sequence;
    `uvm_object_param_utils(uvm_pcie_adapter::sequence_base)
    `uvm_declare_p_sequencer (uvm_pcie_adapter::sequencer)

    protected uvm_reset::sequence_start m_reset;

    protected uvm_common::sequence_library#(uvm_pcie::config_sequence, uvm_pcie::header) m_pcie_cq;
    protected uvm_common::sequence_library#(uvm_pcie::config_sequence, uvm_pcie::header) m_pcie_rc;
    protected uvm_common::sequence_library#(uvm_pcie::config_sequence, uvm_pcie::header) m_mfb_rq;
    protected uvm_common::sequence_library#(uvm_pcie::config_sequence, uvm_pcie::header) m_mfb_cc;

    protected logic stop;

    function new(string name = "logic_vector_sequence");
        super.new(name);
    endfunction

    task reset();
        //HOTFIX:
        fork
            assert(m_reset.randomize());
            m_reset.start(p_sequencer.m_reset);
        join_none;
    endtask

    task body_cq();
        #(300ns);
        while(stop == 0) begin
            assert(m_pcie_cq.randomize());
            m_pcie_cq.start(p_sequencer.m_pcie_cq);
        end
    endtask

    task body_cc();
        #(300ns);
        while(stop == 0) begin
            assert(m_mfb_cc.randomize());
            m_mfb_cc.start(p_sequencer.m_mfb_cc);
        end
    endtask

    task body_rq();
        #(300ns);
        while(stop == 0) begin
            assert(m_mfb_rq.randomize());
            m_mfb_rq.start(p_sequencer.m_mfb_rq);
        end
    endtask

    task body_rc();
        #(300ns);
        while(stop == 0) begin
            assert(m_pcie_rc.randomize());
            m_pcie_rc.start(p_sequencer.m_pcie_rc);
        end
    endtask

    task body();

        m_reset = uvm_reset::sequence_start::type_id::create("m_reset", m_sequencer);

        m_pcie_cq = uvm_pcie::sequence_request_lib::type_id::create("m_pcie_cq", m_sequencer);
        m_pcie_cq.init_sequence();
        m_pcie_cq.min_random_count = 10;
        m_pcie_cq.max_random_count = 20;

        m_pcie_rc = uvm_pcie::sequence_comp_lib::type_id::create("m_pcie_rc", m_sequencer);
        m_pcie_rc.init_sequence();
        m_pcie_rc.min_random_count = 10;
        m_pcie_rc.max_random_count = 20;

        m_mfb_rq = uvm_pcie::sequence_request_lib::type_id::create("m_mfb_rq", m_sequencer);
        m_mfb_rq.init_sequence();
        m_mfb_rq.min_random_count = 10;
        m_mfb_rq.max_random_count = 20;

        m_mfb_cc = uvm_pcie::sequence_comp_lib::type_id::create("m_mfb_cc", m_sequencer);
        m_mfb_cc.init_sequence();
        m_mfb_cc.min_random_count = 10;
        m_mfb_cc.max_random_count = 20;

        stop = 0;

        fork
            body_cq();
            body_cc();
            body_rq();
            body_rc();
            reset();
            begin
                #(2ms);
                stop = 1'b1;
            end
        join
    endtask

endclass

