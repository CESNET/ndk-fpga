//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W, DEVICE, ENDPOINT_TYPE, CC_MFB_BLOCK_SIZE) extends uvm_scoreboard;

    `uvm_component_utils(uvm_pcie_adapter::scoreboard #(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W, DEVICE, ENDPOINT_TYPE, CC_MFB_BLOCK_SIZE))

    localparam IS_INTEL_DEV = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");

    // Analysis components.
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(CQ_MFB_ITEM_WIDTH))    analysis_imp_avst_down_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(AVST_DOWN_META_W))           analysis_imp_avst_down_meta;
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(CC_MFB_ITEM_WIDTH))    analysis_imp_avst_up_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(AVST_UP_META_W))             analysis_imp_avst_up_meta;

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(CQ_MFB_ITEM_WIDTH))    analysis_imp_axi_cq_data;
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(CC_MFB_ITEM_WIDTH))    analysis_imp_axi_cc_data;
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(RC_MFB_ITEM_WIDTH))    analysis_imp_axi_rc_data;
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(RQ_MFB_ITEM_WIDTH))    analysis_imp_axi_rq_data;

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(CQ_MFB_ITEM_WIDTH))    analysis_imp_mfb_cq_data;
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(CC_MFB_ITEM_WIDTH))    analysis_imp_mfb_cc_data;
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(RC_MFB_ITEM_WIDTH))    analysis_imp_mfb_rc_data;
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(RQ_MFB_ITEM_WIDTH))    analysis_imp_mfb_rq_data;

    uvm_analysis_export #(uvm_logic_vector::sequence_item#(CQ_MFB_META_W))             analysis_imp_mfb_cq_meta;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(CC_MFB_META_W))             analysis_imp_mfb_cc_meta;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(RC_MFB_META_W))             analysis_imp_mfb_rc_meta;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(RQ_MFB_META_W))             analysis_imp_mfb_rq_meta;

    uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(RC_MFB_ITEM_WIDTH))                        mfb_rc_data_cmp;
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(RC_MFB_META_W))                                  mfb_rc_meta_cmp;
    uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(CQ_MFB_ITEM_WIDTH))                        mfb_cq_data_cmp;
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(CQ_MFB_META_W))                                  mfb_cq_meta_cmp;
    uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(CC_MFB_ITEM_WIDTH))                        axi_cc_data_cmp;
    uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(RQ_MFB_ITEM_WIDTH))                        axi_rq_data_cmp;
    uvm_pcie_adapter::scoreboard_mfb #(CC_MFB_BLOCK_SIZE, uvm_logic_vector_array::sequence_item#(CC_MFB_ITEM_WIDTH)) avst_up_data_cmp;
    uvm_common::comparer_unordered #(uvm_logic_vector::sequence_item#(AVST_UP_META_W))                              avst_up_meta_cmp;

    model_intel #(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W, ENDPOINT_TYPE) m_model_intel;
    model_xilinx #(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W) m_model_xilinx;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        // INPUT Analysis ports
        if (IS_INTEL_DEV) begin
            analysis_imp_avst_up_data   = new("analysis_imp_avst_up_data"  , this);
            analysis_imp_avst_up_meta   = new("analysis_imp_avst_up_meta"  , this);
            // OUTPUT TLM FIFOs
            analysis_imp_mfb_cq_meta    = new("analysis_imp_mfb_cq_meta", this);
            analysis_imp_mfb_rc_meta    = new("analysis_imp_mfb_rc_meta", this);
        end else begin
            analysis_imp_axi_cc_data   = new("analysis_imp_axi_cc_data", this);
            analysis_imp_axi_rq_data   = new("analysis_imp_axi_rq_data", this);
        end

        analysis_imp_mfb_cq_data   = new("analysis_imp_mfb_cq_data", this);
        analysis_imp_mfb_rc_data   = new("analysis_imp_mfb_rc_data", this);

    endfunction

    function int unsigned used();
        int unsigned ret = 0;

        ret |= mfb_rc_data_cmp.used();
        ret |= mfb_cq_data_cmp.used();
        if (IS_INTEL_DEV) begin
            ret |= mfb_rc_meta_cmp.used();
            ret |= mfb_cq_meta_cmp.used();
            ret |= avst_up_data_cmp.used();
            ret |= avst_up_meta_cmp.used();
        end else begin
            ret |= axi_cc_data_cmp.used();
            ret |= axi_rq_data_cmp.used();
        end

        return ret;
    endfunction

    function int unsigned errors();
        int unsigned ret = 0;

        ret |= mfb_rc_data_cmp.errors != 0;
        ret |= mfb_cq_data_cmp.errors != 0;
        if (IS_INTEL_DEV) begin
            ret |= mfb_rc_meta_cmp.errors != 0;
            ret |= mfb_cq_meta_cmp.errors != 0;
            ret |= avst_up_data_cmp.errors != 0;
            ret |= avst_up_meta_cmp.errors != 0;
        end else begin
            ret |= axi_cc_data_cmp.errors != 0;
            ret |= axi_rq_data_cmp.errors != 0;
        end

        return ret;
    endfunction

    function string compared();
        string ret = "\n";

        $swrite(ret, "%s\tMFB RC DATA COMPARED: %0d\n", ret, mfb_rc_data_cmp.compared);
        $swrite(ret, "%s\tMFB CQ DATA COMPARED: %0d\n", ret, mfb_cq_data_cmp.compared);
        if (IS_INTEL_DEV) begin
            $swrite(ret, "%s\tMFB RC META COMPARED: %0d\n", ret, mfb_rc_meta_cmp.compared);
            $swrite(ret, "%s\tMFB CQ META COMPARED: %0d\n", ret, mfb_cq_meta_cmp.compared);
            $swrite(ret, "%s\tAVST UP DATA COMPARED: %0d\n", ret, avst_up_data_cmp.compared);
            $swrite(ret, "%s\tAVST UP META COMPARED: %0d\n", ret, avst_up_meta_cmp.compared);
        end else begin
            $swrite(ret, "%s\tAXI CC DATA COMPARED: %0d\n", ret, axi_cc_data_cmp.compared);
            $swrite(ret, "%s\tAXI RQ DATA COMPARED: %0d\n", ret, axi_rq_data_cmp.compared);
        end

        return ret;
    endfunction

    function string get_errors();
        string ret = "\n";

        $swrite(ret, "%s\tMFB RC DATA ERRORS: %0d\n", ret, mfb_rc_data_cmp.errors);
        $swrite(ret, "%s\tMFB CQ DATA ERRORS: %0d\n", ret, mfb_cq_data_cmp.errors);
        if (IS_INTEL_DEV) begin
            $swrite(ret, "%s\tMFB RC META ERRORS: %0d\n", ret, mfb_rc_meta_cmp.errors);
            $swrite(ret, "%s\tMFB CQ META ERRORS: %0d\n", ret, mfb_cq_meta_cmp.errors);
            $swrite(ret, "%s\tAVST UP DATA ERRORS: %0d\n", ret, avst_up_data_cmp.errors);
            $swrite(ret, "%s\tAVST UP META ERRORS: %0d\n", ret, avst_up_meta_cmp.errors);
        end else begin
            $swrite(ret, "%s\tAXI CC DATA ERRORS: %0d\n", ret, axi_cc_data_cmp.errors);
            $swrite(ret, "%s\tAXI RQ DATA ERRORS: %0d\n", ret, axi_rq_data_cmp.errors);
        end

        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        if (IS_INTEL_DEV) begin
            m_model_intel = model_intel #(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W, ENDPOINT_TYPE)::type_id::create("m_model_intel", this);

            analysis_imp_avst_down_data = new("analysis_imp_avst_down_data", this);
            analysis_imp_avst_down_meta = new("analysis_imp_avst_down_meta", this);

            avst_up_meta_cmp = uvm_common::comparer_unordered #(uvm_logic_vector::sequence_item#(AVST_UP_META_W))::type_id::create("avst_up_meta_cmp", this);
            avst_up_data_cmp = uvm_pcie_adapter::scoreboard_mfb #(CC_MFB_BLOCK_SIZE, uvm_logic_vector_array::sequence_item#(CC_MFB_ITEM_WIDTH))::type_id::create("avst_up_data_cmp", this);
            mfb_rc_meta_cmp  = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(RC_MFB_META_W))::type_id::create("mfb_rc_meta_cmp", this);
            mfb_cq_meta_cmp  = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(CQ_MFB_META_W))::type_id::create("mfb_cq_meta_cmp", this);

            analysis_imp_mfb_cc_meta = new("analysis_imp_mfb_cc_meta", this);
            analysis_imp_mfb_rq_meta = new("analysis_imp_mfb_rq_meta", this);

            mfb_rc_meta_cmp.model_tr_timeout_set (100ns);
            mfb_cq_meta_cmp.model_tr_timeout_set (100ns);
            avst_up_meta_cmp.model_tr_timeout_set(100ns);
            avst_up_data_cmp.model_tr_timeout_set(100ns);

        end else begin
            m_model_xilinx = model_xilinx #(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W)::type_id::create("m_model_xilinx", this);

            analysis_imp_axi_cq_data    = new("analysis_imp_axi_cq_data", this);
            analysis_imp_axi_rc_data    = new("analysis_imp_axi_rc_data", this);

            axi_cc_data_cmp = uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(CC_MFB_ITEM_WIDTH))::type_id::create("axi_cc_data_cmp", this);
            axi_rq_data_cmp = uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(RQ_MFB_ITEM_WIDTH))::type_id::create("axi_rq_data_cmp", this);

            axi_cc_data_cmp.model_tr_timeout_set(100ns);
            axi_rq_data_cmp.model_tr_timeout_set(100ns);
        end

        mfb_rc_data_cmp = uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(RC_MFB_ITEM_WIDTH))::type_id::create("mfb_rc_data_cmp", this);
        mfb_cq_data_cmp = uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(CQ_MFB_ITEM_WIDTH))::type_id::create("mfb_cq_data_cmp", this);

        mfb_rc_data_cmp.model_tr_timeout_set(100ns);
        mfb_cq_data_cmp.model_tr_timeout_set(100ns);

        analysis_imp_mfb_cc_data = new("analysis_imp_mfb_cc_data", this);
        analysis_imp_mfb_rq_data = new("analysis_imp_mfb_rq_data", this);

    endfunction

    function void connect_phase(uvm_phase phase);

        if (IS_INTEL_DEV) begin
            // Model INTEL INPUTS
            analysis_imp_avst_down_data.connect(m_model_intel.avst_down_data_in.analysis_export);
            analysis_imp_avst_down_meta.connect(m_model_intel.avst_down_meta_in.analysis_export);
            // Model INTEL OUTPUTS
            m_model_intel.avst_up_data_out.connect(avst_up_data_cmp.analysis_imp_model);
            m_model_intel.avst_up_meta_out.connect(avst_up_meta_cmp.analysis_imp_model);
            // DUT INTEL OUTPUTS
            analysis_imp_avst_up_data.connect(avst_up_data_cmp.analysis_imp_dut);
            analysis_imp_avst_up_meta.connect(avst_up_meta_cmp.analysis_imp_dut);
            // Shared INPUTS
            analysis_imp_mfb_cc_data.connect(m_model_intel.mfb_cc_data_in.analysis_export);
            analysis_imp_mfb_cc_meta.connect(m_model_intel.mfb_cc_meta_in.analysis_export);
            analysis_imp_mfb_rq_data.connect(m_model_intel.mfb_rq_data_in.analysis_export);
            analysis_imp_mfb_rq_meta.connect(m_model_intel.mfb_rq_meta_in.analysis_export);
            // Shared Model OUTPUTS
            m_model_intel.mfb_rc_data_out.connect(mfb_rc_data_cmp.analysis_imp_model);
            m_model_intel.mfb_rc_meta_out.connect(mfb_rc_meta_cmp.analysis_imp_model);
            m_model_intel.mfb_cq_data_out.connect(mfb_cq_data_cmp.analysis_imp_model);
            m_model_intel.mfb_cq_meta_out.connect(mfb_cq_meta_cmp.analysis_imp_model);

            analysis_imp_mfb_rc_meta.connect(mfb_rc_meta_cmp.analysis_imp_dut);
            analysis_imp_mfb_cq_meta.connect(mfb_cq_meta_cmp.analysis_imp_dut);
        end else begin
            // Model XILINX INPUTS
            analysis_imp_axi_cq_data.connect(m_model_xilinx.axi_cq_data_in.analysis_export);
            analysis_imp_axi_rc_data.connect(m_model_xilinx.axi_rc_data_in.analysis_export);
            // Model XILINX OUTPUTS
            m_model_xilinx.axi_cc_data_out.connect(axi_cc_data_cmp.analysis_imp_model);
            m_model_xilinx.axi_rq_data_out.connect(axi_rq_data_cmp.analysis_imp_model);
            // DUT XILINX OUTPUTS
            analysis_imp_axi_cc_data.connect(axi_cc_data_cmp.analysis_imp_dut);
            analysis_imp_axi_rq_data.connect(axi_rq_data_cmp.analysis_imp_dut);
            // Shared INPUTS
            analysis_imp_mfb_cc_data.connect(m_model_xilinx.mfb_cc_data_in.analysis_export);
            analysis_imp_mfb_rq_data.connect(m_model_xilinx.mfb_rq_data_in.analysis_export);
            // Shared Model OUTPUTS
            m_model_xilinx.mfb_rc_data_out.connect(mfb_rc_data_cmp.analysis_imp_model);
            m_model_xilinx.mfb_cq_data_out.connect(mfb_cq_data_cmp.analysis_imp_model);
        end
        // Shared DUT OUTPUTS
        analysis_imp_mfb_rc_data.connect(mfb_rc_data_cmp.analysis_imp_dut);
        analysis_imp_mfb_cq_data.connect(mfb_cq_data_cmp.analysis_imp_dut);
    endfunction

    virtual function void report_phase(uvm_phase phase);
        string msg = "\n";
        $swrite(msg, "%s-------------------------------------------------------------------\n", msg);
        $swrite(msg, "%s                           STATISTICS:                             \n", msg);
        $swrite(msg, "%s-------------------------------------------------------------------\n", msg);
        $swrite(msg, "%s%s\n%s \n", msg, this.compared(), this.get_errors());
        $swrite(msg, "%s-------------------------------------------------------------------\n", msg);
        $swrite(msg, "%s-------------------------------------------------------------------\n", msg);

        if (this.used() == 0 && this.errors() == 0) begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", msg), UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------", msg), UVM_NONE)
        end

    endfunction

endclass
