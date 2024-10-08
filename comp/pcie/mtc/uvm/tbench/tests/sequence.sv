//-- sequence.sv:  virtual sequence
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class virt_seq#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PCIE_LEN_MIN, PCIE_LEN_MAX, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_seq#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PCIE_LEN_MIN, PCIE_LEN_MAX, MI_DATA_WIDTH, MI_ADDR_WIDTH))
    `uvm_declare_p_sequencer(uvm_mtc::sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH))


    function new (string name = "virt_seq");
        super.new(name);
    endfunction

    localparam CC_MFB_META_WIDTH = sv_pcie_meta_pack::PCIE_CC_META_WIDTH;
    localparam IS_XILINX_DEV   = (DEVICE == "ULTRASCALE" || DEVICE == "7SERIES");
    uvm_reset::sequence_start                                               m_reset;
    uvm_pcie_hdr::sequence_lib #(IS_XILINX_DEV, PCIE_LEN_MIN, PCIE_LEN_MAX) m_pcie_hdr;

    // uvm_mtc::reg_sequence     m_reg;
    uvm_sequence#(uvm_mfb::sequence_item #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, CC_MFB_META_WIDTH)) m_pcie;
    uvm_mfb::sequence_lib_tx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, CC_MFB_META_WIDTH)               m_pcie_lib;

    uvm_phase phase;

    virtual function void init(uvm_phase phase, uvm_pcie_hdr::sync_tag tag_sync);

        m_reset = uvm_reset::sequence_start::type_id::create("rst_seq");

        m_pcie_hdr = uvm_pcie_hdr::sequence_lib #(IS_XILINX_DEV, PCIE_LEN_MIN, PCIE_LEN_MAX)::type_id::create("m_pcie_hdr");
        m_pcie_hdr.init_sequence();
        m_pcie_hdr.cfg = new();
        m_pcie_hdr.cfg.tag_sync = tag_sync;
        m_pcie_hdr.min_random_count = 50;
        m_pcie_hdr.max_random_count = 100;

        m_pcie_lib  = uvm_mfb::sequence_lib_tx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, CC_MFB_META_WIDTH)::type_id::create("m_pcie_lib");
        m_pcie_lib.init_sequence();
        m_pcie = m_pcie_lib;

        this.phase = phase;
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
        m_pcie_hdr.randomize();
    endfunction

    task body();
        fork
            run_reset();
        join_none

        #(400ns)

        fork
            run_mfb();
        join_none

        m_pcie_hdr.start(p_sequencer.m_packet);
    endtask
endclass
