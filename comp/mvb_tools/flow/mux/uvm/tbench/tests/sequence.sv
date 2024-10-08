// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence#(ITEM_WIDTH, RX_MVB_CNT) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence#(ITEM_WIDTH, RX_MVB_CNT))
    `uvm_declare_p_sequencer(uvm_mvb_mux::virt_sequencer#(ITEM_WIDTH, RX_MVB_CNT))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                      m_reset;
    uvm_logic_vector::sequence_simple#(ITEM_WIDTH) m_logic_vector_sq[RX_MVB_CNT - 1 : 0];
    uvm_logic_vector::sequence_simple#(SEL_WIDTH) m_logic_vector_sel_sq;


    virtual function void init();

        m_reset = uvm_reset::sequence_start::type_id::create("m_reset");
        m_logic_vector_sel_sq = uvm_logic_vector::sequence_simple#(SEL_WIDTH)::type_id::create("m_logic_vector_sel_sq");

        for (int port = 0; port < RX_MVB_CNT; port++)
            m_logic_vector_sq[port] = uvm_logic_vector::sequence_simple#(ITEM_WIDTH)::type_id::create($sformatf("m_logic_vector_sq_%0d", port));

    endfunction

    virtual task run_reset();

        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset);

    endtask // run_reset

    virtual task run_select();
        for (int run = 0; run < RUNS; run++) begin
            m_logic_vector_sel_sq.randomize();
            m_logic_vector_sel_sq.start(p_sequencer.m_logic_vector_sel_scr);
        end
    endtask;

    task body();

        init();

        fork
            run_reset();
        join_none

        #(200ns)

        run_mfb();
        run_select();

    endtask // body

    virtual task run_mvb_port(int unsigned port);
        forever begin
            m_logic_vector_sq[port].randomize();
            m_logic_vector_sq[port].start(p_sequencer.m_logic_vector_scr[port]);
        end
    endtask

    virtual task run_mfb();
        for (int unsigned port = 0; port < RX_MVB_CNT; port++) begin
            fork
                automatic int unsigned x = port;
                run_mvb_port(x);
            join_none;
        end
    endtask

endclass
