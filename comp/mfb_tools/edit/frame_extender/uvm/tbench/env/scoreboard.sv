// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(
    int unsigned MFB_BLOCK_SIZE,
    int unsigned MFB_ITEM_WIDTH,
    int unsigned PKT_MTU,
    int unsigned USERMETA_WIDTH,
    int unsigned RX_MVB_ITEM_WIDTH
) extends uvm_scoreboard;
    `uvm_component_param_utils(
        uvm_mfb_frame_extender::scoreboard #(
            MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH,
            PKT_MTU,
            USERMETA_WIDTH,
            RX_MVB_ITEM_WIDTH
        ))

    // RX analysis exports
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) analysis_export_rx_mfb;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(RX_MVB_ITEM_WIDTH))    analysis_export_rx_mvb;

    // TX analysis exports
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) analysis_export_tx_mfb_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(USERMETA_WIDTH))       analysis_export_tx_mfb_meta;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(USERMETA_WIDTH))       analysis_export_tx_mvb;

    // Comparers
    model_data_comparer          #(MFB_ITEM_WIDTH)                                    comparer_mfb_data;
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(USERMETA_WIDTH)) comparer_mfb_meta;
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(USERMETA_WIDTH)) comparer_mvb;

    // Model
    model #(MFB_ITEM_WIDTH, PKT_MTU, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH) m_model;
    // Meta splitter
    meta_splitter #(USERMETA_WIDTH, RX_MVB_ITEM_WIDTH) m_meta_splitter;

    // High-level coverage model
    coverage_model #(MFB_BLOCK_SIZE, PKT_MTU, RX_MVB_ITEM_WIDTH-USERMETA_WIDTH) m_coverage_model;

    // Contructor
    function new(string name = "scoreboard", uvm_component parent = null);
        super.new(name, parent);

        analysis_export_rx_mfb      = new("analysis_export_rx_mfb", this);
        analysis_export_rx_mvb      = new("analysis_export_rx_mvb", this);
        analysis_export_tx_mfb_data = new("analysis_export_tx_mfb_data", this);
        analysis_export_tx_mfb_meta = new("analysis_export_tx_mfb_meta", this);
        analysis_export_tx_mvb      = new("analysis_export_tx_mvb", this);
    endfunction

    function int unsigned success();
        int unsigned result = 1;
        result &= comparer_mfb_data.success();
        result &= comparer_mfb_meta.success();
        result &= comparer_mvb     .success();
        return result;
    endfunction

    function int unsigned used();
        int unsigned result = 0;
        result |= comparer_mfb_data.used();
        result |= comparer_mfb_meta.used();
        result |= comparer_mvb     .used();
        result |= m_model          .used();
        return result;
    endfunction

    function void build_phase(uvm_phase phase);
        // verilog_lint: waive line-length
        comparer_mfb_data = model_data_comparer          #(MFB_ITEM_WIDTH)                                   ::type_id::create("comparer_mfb_data", this);
        // verilog_lint: waive line-length
        comparer_mfb_meta = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(USERMETA_WIDTH))::type_id::create("comparer_mfb_meta", this);
        // verilog_lint: waive line-length
        comparer_mvb      = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(USERMETA_WIDTH))::type_id::create("comparer_mvb", this);
        comparer_mfb_data.model_tr_timeout_set(2000us);
        comparer_mfb_meta.model_tr_timeout_set(2000us);
        comparer_mvb     .model_tr_timeout_set(2000us);

        m_model         = model         #(
            MFB_ITEM_WIDTH,
            PKT_MTU,
            USERMETA_WIDTH,
            RX_MVB_ITEM_WIDTH
        )::type_id::create("m_model", this);
        m_meta_splitter = meta_splitter #(
            USERMETA_WIDTH,
            RX_MVB_ITEM_WIDTH
        ) ::type_id::create("m_meta_splitter", this);

        m_coverage_model = coverage_model #(
            MFB_BLOCK_SIZE,
            PKT_MTU,
            RX_MVB_ITEM_WIDTH-USERMETA_WIDTH
        )::type_id::create("m_coverage_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // RX MVB -> Meta splitter
        analysis_export_rx_mvb.connect(m_meta_splitter.analysis_export);
        // RX MFB -> Model
        analysis_export_rx_mfb.connect(m_model.in_data.analysis_export);

        // Meta splitter -> Model
        m_meta_splitter.analysis_port_meta     .connect(m_model.in_meta.analysis_export);
        m_meta_splitter.analysis_port_extension.connect(m_model.in_extension.analysis_export);

        // Model data -> MFB data comparer
        m_model.out_data.connect(comparer_mfb_data.analysis_imp_model);
        // Model meta -> MFB meta comparer
        m_model.out_meta.connect(comparer_mfb_meta.analysis_imp_model);
        // Meta splitter -> MVB comparer
        m_meta_splitter.analysis_port_meta.connect(comparer_mvb.analysis_imp_model);

        // Meta splitter -> Coverage model
        m_meta_splitter.analysis_port_extension.connect(m_coverage_model.analysis_export);

        // TX MFB data -> MFB data comparer
        analysis_export_tx_mfb_data.connect(comparer_mfb_data.analysis_imp_dut);
        // TX MFB meta -> MFB meta comparer
        analysis_export_tx_mfb_meta.connect(comparer_mfb_meta.analysis_imp_dut);
        // TX MFB -> MVB comparer
        analysis_export_tx_mvb.connect(comparer_mvb.analysis_imp_dut);
    endfunction

    function void report_phase(uvm_phase phase);
        super.report_phase(phase);

        if (this.success() && this.used() == 0) begin
            `uvm_info(
                get_type_name(),
                // verilog_lint: waive line-length
                "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------",
                UVM_NONE)
        end else begin
            `uvm_info(get_type_name(),
                      "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------"
                          ,
                      UVM_NONE)
        end
    endfunction

endclass
