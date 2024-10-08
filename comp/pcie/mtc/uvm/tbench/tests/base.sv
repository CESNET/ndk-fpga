//-- base.sv: Basic test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class mfb_rx_no_gaps#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) extends uvm_logic_vector_array_mfb::sequence_lib_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
  `uvm_object_param_utils(mfb_rx_no_gaps#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))
  `uvm_sequence_library_utils(mfb_rx_no_gaps#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    function new(string name = "mfb_rx_no_gaps");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(uvm_logic_vector_array_mfb::config_sequence param_cfg = null);
        super.init_sequence(param_cfg);

        this.add_sequence(uvm_logic_vector_array_mfb::seqv_no_inframe_gap_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
    endfunction
endclass

class base extends uvm_test;
    typedef uvm_component_registry#(test::base, "test::base") type_id;

    localparam CQ_MFB_META_WIDTH = sv_pcie_meta_pack::PCIE_CQ_META_WIDTH;

    uvm_mtc::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE, MI_DATA_WIDTH, MI_ADDR_WIDTH) m_env;
    virt_seq#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PCIE_LEN_MIN, PCIE_LEN_MAX, MI_DATA_WIDTH, MI_ADDR_WIDTH) m_vseq;

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    static function type_id get_type();
        return type_id::get();
    endfunction

    function string get_type_name();
        return get_type().get_type_name();
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array_mfb::sequence_lib_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH,
                                                     CQ_MFB_META_WIDTH)::type_id::set_inst_override(mfb_rx_no_gaps#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE,
                                                                                                                    MFB_ITEM_WIDTH, CQ_MFB_META_WIDTH
                                                                                                                    )::get_type(),{this.get_full_name(), ".m_env.m_env_cq.*"});

        m_env = uvm_mtc::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_env", this);
        m_vseq = virt_seq#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PCIE_LEN_MIN, PCIE_LEN_MAX, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_vseq");
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    virtual task run_phase(uvm_phase phase);
        time time_start;

        //RISE OBJECTION
        phase.raise_objection(this);

        m_vseq.init(phase, m_env.tag_sync);
        m_vseq.randomize();
        m_vseq.start(m_env.m_sequencer);

        time_start = $time();
        while((time_start + 200us) > $time() && m_env.sc.used()) begin
            #(600ns);
        end

        phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction

endclass
