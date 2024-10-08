//-- sequence.sv:  virtual sequence
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class virt_seq#(PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH, CHANNELS) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_seq#(PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH, CHANNELS))
    `uvm_declare_p_sequencer(uvm_dma_ll::sequencer#(PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH, CHANNELS))

    function new (string name = "virt_seq");
        super.new(name);
    endfunction

    uvm_reset::sequence_start              m_reset;

    uvm_byte_array::sequence_lib m_packet;

    uvm_dma_ll::reg_sequence#(CHANNELS)     m_reg;
    uvm_sequence#(uvm_mfb::sequence_item #(PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH)) m_pcie;

    local logic m_done;

    virtual function void init(uvm_dma_ll::regmodel#(CHANNELS) m_regmodel);
        uvm_mfb::sequence_lib_tx#(PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH) m_pcie_lib;

        m_reset = uvm_reset::sequence_start::type_id::create("rst_seq");

        m_packet = uvm_byte_array::sequence_lib::type_id::create("m_packet");
        m_packet.init_sequence();
        m_packet.min_random_count = 80;
        m_packet.max_random_count = 100;
        m_packet.cfg = new();
        m_packet.cfg.array_size_set(60,PKT_SIZE_MAX);

        m_reg    =  uvm_dma_ll::reg_sequence#(CHANNELS)::type_id::create("m_reg");
        m_reg.m_regmodel = m_regmodel;

        m_pcie_lib  = uvm_mfb::sequence_lib_tx#(PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH)::type_id::create();
        m_pcie_lib.init_sequence();
        m_pcie = m_pcie_lib;
    endfunction

    virtual task run_mfb();
        forever begin
            assert(m_pcie.randomize());
            m_pcie.start(p_sequencer.m_pcie);
        end
    endtask

    virtual task run_reset();
        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset);
    endtask

    function void pre_randomize();
         m_packet.randomize();
         m_reg.randomize();
    endfunction

    task body();
        m_done = 0;

        fork
            run_reset();
            begin
                #(200ns)
                m_reg.start(null);
            end
        join_none

        #(50ns)

        fork
            begin
                m_packet.start(p_sequencer.m_packet.m_data);
                m_done = 1;
            end

            run_mfb();
        join_any

        wait((& m_done) == 1);
    endtask
endclass
