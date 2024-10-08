// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence#(DATA_WIDTH, TUSER_WIDTH, MFB_REGIONS, MFB_ITEM_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence#(DATA_WIDTH, TUSER_WIDTH, MFB_REGIONS, MFB_ITEM_WIDTH))
    `uvm_declare_p_sequencer(uvm_pcie_cc_mfb2axi::virt_sequencer#(DATA_WIDTH, TUSER_WIDTH, MFB_REGIONS, MFB_ITEM_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH)                                      m_logic_vector_array_sq_lib;
    uvm_axi::sequence_lib_tx#(DATA_WIDTH, TUSER_WIDTH, MFB_REGIONS) m_pcie_lib;

    virtual function void init();

        m_logic_vector_array_sq_lib = uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH)::type_id::create("m_logic_vector_array_sq_lib");
        m_pcie_lib              = uvm_axi::sequence_lib_tx#(DATA_WIDTH, TUSER_WIDTH, MFB_REGIONS)::type_id::create("m_pcie_lib");

        m_logic_vector_array_sq_lib.init_sequence();
        m_logic_vector_array_sq_lib.min_random_count = 50;
        m_logic_vector_array_sq_lib.max_random_count = 100;
        m_logic_vector_array_sq_lib.randomize();

        m_pcie_lib.init_sequence();
        m_pcie_lib.min_random_count = 100;
        m_pcie_lib.max_random_count = 200;

    endfunction

    virtual task run_mfb();
        forever begin
            assert(m_pcie_lib.randomize());
            m_pcie_lib.start(p_sequencer.m_pcie);
        end
    endtask

    task body();

        init();

        fork
            run_mfb();
        join_none

        fork
            run_axi_data();
        join_any

    endtask

    virtual task run_axi_data();
        m_logic_vector_array_sq_lib.start(p_sequencer.m_logic_vector_array_scr);
    endtask

endclass
