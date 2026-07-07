// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    int unsigned PKT_MTU
) extends uvm_scoreboard;
    `uvm_component_param_utils(
        uvm_mfb_frame_trimmer::scoreboard #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, PKT_MTU))

    // RX analysis exports
    // verilog_lint: waive line-length
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH))               analysis_export_rx_mfb_data;
    // verilog_lint: waive line-length
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(META_WIDTH+1+$clog2(PKT_MTU+1))) analysis_export_rx_mfb_meta;

    // TX analysis exports
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)) analysis_export_tx_mfb_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(META_WIDTH))       analysis_export_tx_mfb_meta;

    // Comparers
    uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)) comparer_data;
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(META_WIDTH))       comparer_meta;

    // Model
    model #(ITEM_WIDTH, PKT_MTU) m_model;
    // Meta splitter
    meta_splitter #(META_WIDTH, PKT_MTU) m_meta_splitter;

    // High-level coverage model
    coverage_model #(BLOCK_SIZE, ITEM_WIDTH, PKT_MTU) m_coverage_model;

    // Contructor
    function new(string name = "scoreboard", uvm_component parent = null);
        super.new(name, parent);

        analysis_export_rx_mfb_data = new("analysis_export_rx_mfb_data", this);
        analysis_export_rx_mfb_meta = new("analysis_export_rx_mfb_meta", this);
        analysis_export_tx_mfb_data = new("analysis_export_tx_mfb_data", this);
        analysis_export_tx_mfb_meta = new("analysis_export_tx_mfb_meta", this);
    endfunction

    function int unsigned success();
        int unsigned result = 1;
        result &= comparer_data.success();
        result &= comparer_meta.success();
        return result;
    endfunction

    function int unsigned used();
        int unsigned result = 0;
        result |= comparer_data.used();
        result |= comparer_meta.used();
        return result;
    endfunction

    function void build_phase(uvm_phase phase);
        // verilog_lint: waive line-length
        comparer_data = uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH))::type_id::create("comparer_data", this);
        // verilog_lint: waive line-length
        comparer_meta = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(META_WIDTH))      ::type_id::create("comparer_meta", this);
        comparer_data.model_tr_timeout_set(2000us);
        comparer_meta.model_tr_timeout_set(2000us);

        m_model         = model         #(ITEM_WIDTH, PKT_MTU)::type_id::create("m_model", this);
        m_meta_splitter = meta_splitter #(META_WIDTH, PKT_MTU)::type_id::create("m_meta_splitter", this);

        m_coverage_model = coverage_model #(BLOCK_SIZE, ITEM_WIDTH, PKT_MTU)::type_id::create("m_coverage_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // RX meta -> Meta splitter
        analysis_export_rx_mfb_meta.connect(m_meta_splitter.analysis_export);
        // Meta splitter -> Model
        m_meta_splitter.analysis_port_len.connect(m_model.in_trim.analysis_export);
        // Meta splitter -> Meta comparer
        m_meta_splitter.analysis_port_meta.connect(comparer_meta.analysis_imp_model);

        // RX data -> Model -> Data comparer
        analysis_export_rx_mfb_data.connect(m_model.in_data.analysis_export);
        m_model.out_data           .connect(comparer_data.analysis_imp_model);

        // RX data -> Coverage model
        analysis_export_rx_mfb_data.connect(m_coverage_model.in_data.analysis_export);
        // Meta splitter -> Coverage model
        m_meta_splitter.analysis_port_len.connect(m_coverage_model.in_trim.analysis_export);

        // TX data -> Data comparer
        analysis_export_tx_mfb_data.connect(comparer_data.analysis_imp_dut);
        // TX meta -> Meta comparer
        analysis_export_tx_mfb_meta.connect(comparer_meta.analysis_imp_dut);
    endfunction

    function void report_phase(uvm_phase phase);
        string msg = "\n";

        if (m_model.in_data.used() > 0 || m_model.in_trim.used() > 0) begin
            msg = {
                msg,
                $sformatf(
                    "\n\tSOME TRANSACTIONS ARE STUCK INSIDE THE MODEL\n\tDATA:%0d\n\tTRIM:%0d",
                    m_model.in_data.used(),
                    m_model.in_trim.used()
                )
            };
        end

        if (this.success() && this.used() == 0) begin
            `uvm_info(
                get_type_name(), {
                msg,
                "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"
                }, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {
                      msg,
                      "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------"
                      }, UVM_NONE)
        end
    endfunction

endclass
