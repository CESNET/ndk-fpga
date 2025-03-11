// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(int unsigned RX_ITEMS, int unsigned TX_ITEMS, int unsigned ITEM_WIDTH) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_mvb_shakedown::scoreboard #(RX_ITEMS, TX_ITEMS, ITEM_WIDTH))

    // RX analysis exports
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(ITEM_WIDTH)) analysis_export_rx_mvb;

    // TX analysis exports
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(ITEM_WIDTH)) analysis_export_tx_mvb[TX_ITEMS];
    uvm_analysis_export #(read_command_item #(TX_ITEMS))                 analysis_export_tx_read_command;

    // Comparers
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(ITEM_WIDTH)) comparer[TX_ITEMS];

    // Model
    model #(RX_ITEMS, TX_ITEMS, ITEM_WIDTH) m_model;

    // High-level coverage model
    hl_coverage_model #(TX_ITEMS) m_coverage_model;

    // Contructor
    function new(string name = "scoreboard", uvm_component parent = null);
        super.new(name, parent);

        analysis_export_rx_mvb = new("analysis_export_rx_mvb", this);
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            analysis_export_tx_mvb[i] = new($sformatf("analysis_export_tx_mvb_%0d", i), this);
        end
        analysis_export_tx_read_command = new("analysis_export_tx_read_command", this);
    endfunction

    function int unsigned success();
        int unsigned result = 1;
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            result &= comparer[i].success();
        end
        return result;
    endfunction

    function int unsigned used();
        int unsigned result = 0;
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            result |= comparer[i].used();
        end
        return result;
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            comparer[i] = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(ITEM_WIDTH))::type_id::create($sformatf("comparer_%0d", i), this);
            comparer[i].model_tr_timeout_set(200us);
        end

        m_model = model #(RX_ITEMS, TX_ITEMS, ITEM_WIDTH)::type_id::create("m_model", this);

        m_coverage_model = hl_coverage_model #(TX_ITEMS)::type_id::create("m_coverage_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // RX -> Model => Comparers
        analysis_export_rx_mvb.connect(m_model.in_data.analysis_export);
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            m_model.out[i].connect(comparer[i].analysis_imp_model);
        end

        // TX read commands -> Model
        analysis_export_tx_read_command.connect(m_model.in_read_command.analysis_export);
        // TX read commands -> Coverage model
        analysis_export_tx_read_command.connect(m_coverage_model.analysis_export);

        // TX data => Comparers
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            analysis_export_tx_mvb[i].connect(comparer[i].analysis_imp_dut);
        end
    endfunction

    function void report_phase(uvm_phase phase);
        string msg = "\n";

        super.report_phase(phase);

        if (m_model.in_data.used() > 0 || m_model.in_read_command.used() > 0) begin
            msg = { msg, $sformatf("\n\tSOME TRANSACTIONS ARE STUCK INSIDE THE MODEL\n\tDATA:%0d\n\tPORT NUMBER:%0d", m_model.in_data.used(), m_model.in_read_command.used()) };
        end

        if (this.success() && this.used() == 0) begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------"}, UVM_NONE)
        end
    endfunction

endclass
