// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(MVB_ITEM_WIDTH, RX_STREAMS) extends uvm_scoreboard;
    `uvm_component_utils(uvm_mvb_merge_streams_ordered::scoreboard #(MVB_ITEM_WIDTH, RX_STREAMS))

    // Analysis components.
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH))      rx_mvb_analysis_imp [RX_STREAMS -1 : 0];
    uvm_analysis_export #(uvm_logic_vector::sequence_item #($clog2(RX_STREAMS)))  rx_sel_mvb_analysis_imp;
    uvm_analysis_export    #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH))      tx_mvb_analysis_exp;

    // Comparer instance
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH)) cmp;

    // Model instance
    model #(MVB_ITEM_WIDTH, RX_STREAMS) m_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        tx_mvb_analysis_exp = new("tx_mvb_analysis_exp", this);

        for (int port = 0; port < RX_STREAMS; port++) begin
            rx_mvb_analysis_imp[port]  = new($sformatf("rx_mvb_analysis_imp_%0d", port), this);
        end
        rx_sel_mvb_analysis_imp        = new("rx_sel_mvb_analysis_imp", this);

    endfunction

    function void build_phase(uvm_phase phase);
        cmp     = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH))::type_id::create("cmp", this);
        cmp.model_tr_timeout_set(128ns);

        m_model = model #(MVB_ITEM_WIDTH, RX_STREAMS)::type_id::create("m_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Connects input data to the input of the model
        for (int port = 0; port < RX_STREAMS; port++) begin
            rx_mvb_analysis_imp[port].connect(m_model.rx_mvb_analysis_fifo[port].analysis_export);
        end
        rx_sel_mvb_analysis_imp      .connect(m_model.rx_sel_mvb_analysis_fifo  .analysis_export);

        // Connects output data of the DUT
        tx_mvb_analysis_exp.connect(cmp.analysis_imp_dut);

        // Connects output data of the model
        m_model.tx_mvb_analysis_imp.connect(cmp.analysis_imp_model);
    endfunction

    function void report_phase(uvm_phase phase);
        string msg = "\n";

        if (cmp.success() && cmp.used() == 0) begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------"}, UVM_NONE)
        end
    endfunction
endclass
