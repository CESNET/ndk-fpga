//-- test.sv: Verification test
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class test_base extends uvm_test;
    `uvm_component_utils(test::test_base);

    localparam IS_INTEL_DEV  = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");
    localparam AXI_ITEMS     = CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE;

    uvm_pcie_adapter::env #(
        RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE,
        RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE,
        CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE,
        CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE,
        DEVICE
    ) m_env;

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        if (ENDPOINT_TYPE == "R_TILE") begin
            uvm_mfb::sequence_lib_tx #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, 32, sv_pcie_meta_pack::PCIE_RC_META_WIDTH)::type_id::set_inst_override(
                uvm_mfb::sequence_lib_tx_speed#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, 32, sv_pcie_meta_pack::PCIE_RC_META_WIDTH)::get_type(),
                "m_env.m_mfb_rc_env.seq_mfb", this
            );
        end

        if (IS_INTEL_DEV) begin
            uvm_pcie::root::type_id::set_inst_override(
                uvm_pcie_avst::root#(RQ_MFB_REGIONS, RQ_MFB_BLOCK_SIZE, 27, STRADDLING)::get_type(),
                "m_env.m_pcie", this);
        end else begin
            uvm_pcie::root::type_id::set_inst_override(
                uvm_pcie_axi::root#(AXI_ITEMS, DEVICE, STRADDLING)::get_type(),
                "m_env.m_pcie", this);
        end

        super.build_phase(phase);

        m_env = uvm_pcie_adapter::env #(
            RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE,
            RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE,
            CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE,
            CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE,
            DEVICE
        )::type_id::create("m_env", this);
    endfunction

    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_pkg::uvm_top.print_topology();
        uvm_factory::get().print();
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    virtual task run_phase(uvm_phase phase);
        time stop;
        uvm_pcie_adapter::sequence_base m_vseq;


        m_vseq = uvm_pcie_adapter::sequence_base::type_id::create("m_vseq", this);

        phase.raise_objection(this, "Start of rx sequence");

        assert(m_vseq.randomize());
        m_vseq.start(m_env.m_sequencer);

        stop = $time + 1ms;
        while (m_env.used() == 1 && stop > $time) begin
            #(600ns);
        end

        phase.drop_objection(this, "End of rx sequence");
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass
