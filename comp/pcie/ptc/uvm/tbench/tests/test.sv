//-- test.sv: Verification test
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    localparam IS_INTEL = (DEVICE == "STRATIX10" ||  DEVICE == "AGILEX") ? 1'b1 : 1'b0;
    localparam RQ_AXI_ITEMS = (IS_INTEL == 0) ? MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE       : 16;
    localparam RC_AXI_ITEMS = (IS_INTEL == 0) ? MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE : 16;


    uvm_ptc::env #(MVB_UP_ITEMS,
                   DMA_MVB_UP_ITEMS,   DMA_MFB_UP_REGIONS,   MFB_UP_REG_SIZE,   MFB_UP_BLOCK_SIZE,
                   DMA_MVB_DOWN_ITEMS, DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE,
                   DMA_PORTS, PCIE_TAG_WIDTH, 0
                  ) m_env;

    logic [DMA_PORTS-1 : 0] event_vseq;

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);

        //REWRITE PCIE
        if (DEVICE == "VIRTEX6" || DEVICE == "7SERIES" || DEVICE == "ULTRASCALE" ) begin
            uvm_pcie::env_tx::type_id::set_inst_override(
                    uvm_pcie_axi::env_tx#(RQ_AXI_ITEMS, uvm_pcie_axi::AXI_RQ, DEVICE, PCIE_STRADDLING
            )::get_type(), "m_env.*", this);

            uvm_pcie::env_rx::type_id::set_inst_override(
                    uvm_pcie_axi::env_rx#(RC_AXI_ITEMS, uvm_pcie_axi::AXI_RC, DEVICE, PCIE_STRADDLING
            )::get_type(), "m_env.*", this);

        end else if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
            uvm_pcie::env_tx::type_id::set_inst_override(
                uvm_pcie_mfb::env_mvb_tx #(MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE,
                                      uvm_pcie_mfb::MFB_RQ, uvm_pcie_mfb::DEV_INTEL
                )::get_type(), "m_env.*", this);

            uvm_pcie::env_rx::type_id::set_inst_override(
                uvm_pcie_mfb::env_rx #(MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE,
                                      uvm_pcie_mfb::MFB_RC, uvm_pcie_mfb::MFB_META_SOF, PCIE_STRADDLING, uvm_pcie_mfb::DEV_INTEL
                )::get_type(), "m_env.*", this);

        end else begin
            `uvm_fatal(this.get_full_name(), "\n\tUNSUPPORTED DEVICE");
        end

        m_env = uvm_ptc::env #(MVB_UP_ITEMS,
                               DMA_MVB_UP_ITEMS,   DMA_MFB_UP_REGIONS,   MFB_UP_REG_SIZE,   MFB_UP_BLOCK_SIZE,
                               DMA_MVB_DOWN_ITEMS, DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE,
                               DMA_PORTS, PCIE_TAG_WIDTH, 0
                )::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    virtual task run_phase(uvm_phase phase);
        time time_start;
        uvm_ptc::sequence_base#(PCIE_TAG_WIDTH, DMA_PORTS) seq;

        seq = uvm_ptc::sequence_base#(PCIE_TAG_WIDTH, DMA_PORTS)::type_id::create("seq", this);

        phase.raise_objection(this);

        assert(seq.randomize());
        seq.start(m_env.m_sequencer);

        time_start = $time();
        do begin
            #(600ns);
        end while((time_start + 10ms) > $time() && m_env.used());
        phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction

endclass
