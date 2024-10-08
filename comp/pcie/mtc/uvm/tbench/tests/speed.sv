//-- test.sv: Verification test
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class virt_seq_full_speed#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PCIE_LEN_MIN, PCIE_LEN_MAX, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends virt_seq#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH,
                                                                                                                                                                     PCIE_LEN_MIN, PCIE_LEN_MAX, MI_DATA_WIDTH, MI_ADDR_WIDTH);

    `uvm_object_param_utils(test::virt_seq_full_speed#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PCIE_LEN_MIN, PCIE_LEN_MAX, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    `uvm_declare_p_sequencer(uvm_mtc::sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    function new (string name = "virt_seq_full_speed");
        super.new(name);
    endfunction

    virtual function void init(uvm_phase phase, uvm_pcie_hdr::sync_tag tag_sync);
        super.init(phase, tag_sync);
        m_pcie = uvm_mfb::sequence_full_speed_tx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE,
                                                         MFB_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CC_META_WIDTH)::type_id::create("m_pcie_lib");
    endfunction
endclass

class mfb_rx_speed#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) extends uvm_logic_vector_array_mfb::sequence_lib_rx#(REGIONS, REGION_SIZE,
                                                                                                                                   BLOCK_SIZE, ITEM_WIDTH,
                                                                                                                                   META_WIDTH);
  `uvm_object_param_utils(    mfb_rx_speed#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))
  `uvm_sequence_library_utils(mfb_rx_speed#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    function new(string name = "mfb_rx_speed");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(uvm_logic_vector_array_mfb::config_sequence param_cfg = null);
        if (param_cfg == null) begin
            this.cfg = new();
        end else begin
            this.cfg = param_cfg;
        end


        this.add_sequence(uvm_logic_vector_array_mfb::sequence_full_speed_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
    endfunction
endclass


class speed extends base;
    typedef uvm_component_registry#(test::speed, "test::speed") type_id;


    localparam CQ_MFB_META_WIDTH = sv_pcie_meta_pack::PCIE_CQ_META_WIDTH;

    uvm_mtc::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE, MI_DATA_WIDTH, MI_ADDR_WIDTH) m_env;

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
                                                     CQ_MFB_META_WIDTH)::type_id::set_inst_override(mfb_rx_speed#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE,
                                                                                                                    MFB_ITEM_WIDTH, CQ_MFB_META_WIDTH
                                                                                                                    )::get_type(),{this.get_full_name(), ".m_env.m_env_cq.*"});

        m_env = uvm_mtc::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    virtual task run_phase(uvm_phase phase);
        virt_seq_full_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PCIE_LEN_MIN, PCIE_LEN_MAX, MI_DATA_WIDTH, MI_ADDR_WIDTH) m_vseq;
        time time_start;

        //CREATE SEQUENCES
        m_vseq = virt_seq_full_speed#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PCIE_LEN_MIN, PCIE_LEN_MAX, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_vseq");

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
