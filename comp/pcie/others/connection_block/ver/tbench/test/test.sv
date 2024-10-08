/*
 * file       : test.sv
 * description: test
 * date       : 2020
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * Copyright (C) 2020 CESNET
 * SPDX-License-Identifier: BSD-3-Clause
*/

///////////////////////////////////////////////////////////////////////////////
// simple test for connection block
class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    /////////////////////
    // variables
    env::env_base m_env;

    /////////////////////
    // functions
    function new(string name, uvm_component parent);
            super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = env::env_base::type_id::create("m_env", this);
    endfunction

    //run virtual sequence on virtual sequencer
    virtual task run_phase(uvm_phase phase);
        env::virtual_sequence seq;

        uvm_component c;
        c = uvm_root::get();
        c.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        seq = env::virtual_sequence::type_id::create("seq");
        seq.randomize();
        seq.set_starting_phase(phase);
        seq.start(m_env.vir_sqr);
    endtask
endclass
