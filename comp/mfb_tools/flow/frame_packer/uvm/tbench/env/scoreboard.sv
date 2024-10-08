// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:   David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(RX_CHANNELS, PKT_MTU, META_WIDTH,  MFB_ITEM_WIDTH) extends uvm_scoreboard;

    `uvm_component_utils(uvm_framepacker::scoreboard #(RX_CHANNELS, PKT_MTU, META_WIDTH,  MFB_ITEM_WIDTH))

    // RX
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH))                   analysis_imp_mfb_rx_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#($clog2(RX_CHANNELS) + $clog2(PKT_MTU+1))) analysis_imp_mvb_rx;

    // TX
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH))  analysis_imp_mfb_tx_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #($clog2(RX_CHANNELS) + $clog2(PKT_MTU+1) + META_WIDTH + 1))       analysis_imp_mvb_tx;

    //Comparer
    uvm_framepacker::comparer_meta #(RX_CHANNELS, PKT_MTU, META_WIDTH)  meta_cmp;
    uvm_framepacker::comparer_superpacket #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) data_cmp;

    //Model
    model #(RX_CHANNELS, PKT_MTU, META_WIDTH,  MFB_ITEM_WIDTH) m_model;

    // Contructor
    function new(string name, uvm_component parent);
        super.new(name, parent);

        analysis_imp_mvb_rx = new("analysis_imp_mvb_rx", this);
        analysis_imp_mvb_tx = new("analysis_imp_mvb_tx", this);

        analysis_imp_mfb_rx_data = new("analysis_imp_mfb_rx_data", this);
        analysis_imp_mfb_tx_data = new("analysis_imp_mfb_tx_data", this);
    endfunction

    function int unsigned success();
        int unsigned ret = 1;
        ret &= data_cmp.success();
        ret &= meta_cmp.success();
        return ret;
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= meta_cmp.used();
        ret |= data_cmp.used();
        ret |= m_model.used();
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        m_model = model #(RX_CHANNELS, PKT_MTU, META_WIDTH,  MFB_ITEM_WIDTH)::type_id::create("m_model", this);
        //data_cmp = uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH))::type_id::create("data_cmp", this);

        data_cmp = uvm_framepacker::comparer_superpacket #(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH))::type_id::create("data_cmp", this);
        data_cmp.model_tr_timeout_set(500us);

        meta_cmp = uvm_framepacker::comparer_meta #(RX_CHANNELS, PKT_MTU, META_WIDTH)::type_id::create("meta_cmp", this);
        meta_cmp.model_tr_timeout_set(500us);
    endfunction

    function void connect_phase(uvm_phase phase);
        //Input of model
        analysis_imp_mfb_rx_data.connect(m_model.data_in.analysis_export);
        analysis_imp_mvb_rx.connect(m_model.meta_in.analysis_export);

        //Connect model output to comparer
        m_model.data_out.connect(data_cmp.analysis_imp_model);
        analysis_imp_mfb_tx_data.connect(data_cmp.analysis_imp_dut);

        m_model.meta_out.connect(meta_cmp.analysis_imp_model);
        analysis_imp_mvb_tx.connect(meta_cmp.analysis_imp_dut);
    endfunction

    virtual function void report_phase(uvm_phase phase);

        if (this.success() && this.used() == 0) begin
            `uvm_info(get_type_name(), $sformatf("\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"), UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf("\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------"), UVM_NONE)
        end

    endfunction
endclass
