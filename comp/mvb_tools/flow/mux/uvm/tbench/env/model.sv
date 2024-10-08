// model.sv: Model of implementation
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class model #(ITEMS, ITEM_WIDTH, RX_MVB_CNT) extends uvm_component;
    `uvm_component_param_utils(uvm_mvb_mux::model#(ITEMS, ITEM_WIDTH, RX_MVB_CNT))

    // Model inputs
    uvm_tlm_analysis_fifo #(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH)) model_mvb_in[RX_MVB_CNT - 1 : 0];
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #($clog2(RX_MVB_CNT))) model_mvb_sel;
    uvm_analysis_port #(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH)) model_mvb_out;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        model_mvb_out = new("model_mvb_out",  this);
        model_mvb_sel = new("model_mvb_sel", this);

        for (int port = 0; port < RX_MVB_CNT; port++) begin
            model_mvb_in[port] = new($sformatf("model_mvb_in_%0d", port), this);
        end
    endfunction // new

    task run_phase(uvm_phase phase);
        uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH) tr_mvb_in;
        uvm_logic_vector::sequence_item #($clog2(RX_MVB_CNT)) tr_mvb_sel;

        int sel = 0;

        forever begin
            model_mvb_sel.get(tr_mvb_sel);
            sel = tr_mvb_sel.data;
            do begin
                model_mvb_in[sel].get(tr_mvb_in);
            end while (tr_mvb_in.src_rdy !== 'b1 || tr_mvb_in.dst_rdy != 'b1);

            model_mvb_out.write(tr_mvb_in);
        end
    endtask
endclass
