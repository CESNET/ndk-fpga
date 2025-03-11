// activity_detector.sv: Generates read commands
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class activity_detector #(int unsigned TX_ITEMS, int unsigned ITEM_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_mvb_shakedown::activity_detector #(TX_ITEMS, ITEM_WIDTH))

    // Inputs
    uvm_tlm_analysis_fifo #(uvm_mvb::sequence_item #(1, ITEM_WIDTH)) in[TX_ITEMS];

    // Outputs
    uvm_analysis_port #(read_command_item #(TX_ITEMS)) analysis_port;

    function new(string name = "activity_detector", uvm_component parent = null);
        super.new(name, parent);

        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            in[i] = new($sformatf("in_%0d", i), this);
        end
        analysis_port = new("analysis_port", this);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_mvb::sequence_item #(1, ITEM_WIDTH) in_item;
        read_command_item #(TX_ITEMS) out_read_command_item;

        forever begin
            out_read_command_item = read_command_item #(TX_ITEMS)::type_id::create("out_read_command_item");

            for (int unsigned i = 0; i < TX_ITEMS; i++) begin
                in[i].get(in_item);

                if (in_item.src_rdy === 1'b1 && in_item.dst_rdy === 1'b1 && in_item.vld === 1'b1) begin
                    out_read_command_item.read[i] = 1'b1;
                end
                else begin
                    out_read_command_item.read[i] = 1'b0;
                end
            end

            if (|out_read_command_item.read > 0) begin
                analysis_port.write(out_read_command_item);
            end
        end
    endtask

endclass
