// request_subscriber.sv: AVMM request subscriber
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Converts uvm_avmm::sequence_item_request to uvm_avmm::request_item
class request_subscriber #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_subscriber #(sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH));
    `uvm_component_param_utils(uvm_avmm::request_subscriber #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // Output port
    uvm_analysis_port #(request_item #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)) analysis_port;

    // Reset
    uvm_reset::sync_terminate reset_sync;

    // Constructor
    function new (string name = "request_subscriber", uvm_component parent = null);
        super.new(name, parent);

        reset_sync    = new();
        analysis_port = new("uvm_analysis_port", this);
    endfunction

    function void write(sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) t);
        request_item #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) item;

        if (reset_sync.has_been_reset()) begin
            return;
        end

        if (t.ready === 1'b1 && (t.read === 1'b1 || t.write === 1'b1)) begin
            item = request_item #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("item");
            item.address = t.address;
            item.burstcount = t.burstcount;
            if (t.read === 1'b1) begin
                item.request_type = READ;
                item.writedata = '0;
            end
            else begin
                item.request_type = WRITE;
                item.writedata = t.writedata;
            end

            analysis_port.write(item);
        end
    endfunction

endclass
