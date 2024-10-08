// model.sv: Model of implementation
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class model #(MVB_ITEM_WIDTH, RX_STREAMS) extends uvm_component;
    `uvm_component_param_utils(uvm_mvb_merge_streams_ordered::model #(MVB_ITEM_WIDTH, RX_STREAMS))

    // Model inputs
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH))      rx_mvb_analysis_fifo [RX_STREAMS -1 : 0];
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #($clog2(RX_STREAMS)))  rx_sel_mvb_analysis_fifo;
    // Model outputs
    uvm_analysis_port     #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH))      tx_mvb_analysis_imp;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        for (int port = 0; port < RX_STREAMS; port++) begin
            rx_mvb_analysis_fifo[port] = new($sformatf("rx_mvb_analysis_fifo_%0d", port), this);
        end
        rx_sel_mvb_analysis_fifo       = new("rx_sel_mvb_analysis_fifo", this);
        tx_mvb_analysis_imp            = new("tx_mvb_analysis_imp",      this);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH)     rx_mvb_tr;
        uvm_logic_vector::sequence_item #($clog2(RX_STREAMS)) rx_sel_mvb_tr;
        int unsigned                                          sel;

        forever begin
            rx_sel_mvb_analysis_fifo.get(rx_sel_mvb_tr);
            sel = rx_sel_mvb_tr.data;

            rx_mvb_analysis_fifo[sel].get(rx_mvb_tr);
            tx_mvb_analysis_imp.write(rx_mvb_tr);
        end
    endtask
endclass
