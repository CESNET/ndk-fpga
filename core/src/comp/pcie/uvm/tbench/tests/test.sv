// test.sv: Verification test
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:   Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    bit timeout;
    uvm_pcie_top::env #(RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, RQ_MFB_META_W,
                                                   RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_META_W,
                                                   CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_META_W,
                                                   CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_META_W,
                                                   ITEM_WIDTH,  DMA_PORTS, PCIE_ENDPOINTS,  PCIE_CONS, DEVICE) m_env;

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_pcie_top::env #(RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, RQ_MFB_META_W,
                                                   RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_META_W,
                                                   CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_META_W,
                                                   CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_META_W,
                                                   ITEM_WIDTH,  DMA_PORTS, PCIE_ENDPOINTS,  PCIE_CONS, DEVICE)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    task run_seq_rx(uvm_phase phase);
        time time_start;


        uvm_pcie_top::sequence_base #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_META_W, CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE,  CQ_MFB_BLOCK_SIZE, CQ_MFB_META_W,
                                                         RQ_MFB_META_W,  CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_META_W, ITEM_WIDTH, DMA_PORTS, PCIE_CONS, PCIE_ENDPOINTS) m_virt_seq;

        m_virt_seq = uvm_pcie_top::sequence_base #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_META_W, CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE,  CQ_MFB_BLOCK_SIZE, CQ_MFB_META_W,
                                                         RQ_MFB_META_W,  CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_META_W, ITEM_WIDTH, DMA_PORTS, PCIE_CONS, PCIE_ENDPOINTS)::type_id::create("m_vseq", this);

        //START TEST
        phase.raise_objection(this, "Start of rx sequence");
        m_virt_seq.init(m_env.m_sequencer);
        assert(m_virt_seq.randomize());
        m_virt_seq.start(m_env.m_sequencer);

        //STOP TEST
        time_start = $time();
        while((time_start + 10ms) > $time() && m_env.m_scoreboard.used()) begin
            #(600ns);
        end
        phase.drop_objection(this, "End of rx sequence");
    endtask

    virtual task run_phase(uvm_phase phase);
        run_seq_rx(phase);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass
