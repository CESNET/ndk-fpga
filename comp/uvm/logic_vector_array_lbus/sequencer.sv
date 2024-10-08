// sequencer.sv: Sequencer for the environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// ======= //
// TX side //
// ======= //

class sequencer_tx extends uvm_sequencer;
    `uvm_component_utils(uvm_logic_vector_array_lbus::sequencer_tx);

    // A lower limit of the request queue to start accepting new items from high-level sequences
    localparam int unsigned REQUEST_QUEUE_SATURATION_THRESHOLD = 10;

    // Sequencers
    uvm_logic_vector_array::sequencer #(8) packet;
    uvm_logic_vector::sequencer       #(1) error;

    // Reset
    uvm_reset::sync_terminate reset_sync;

    // Request queue
    uvm_lbus::sequence_item request_queue[$];

    // Constructor
    function new(string name = "sequencer_tx", uvm_component parent = null);
        super.new(name, parent);
        reset_sync = new();
    endfunction

    task run_phase(uvm_phase phase);
        run_receiver();
    endtask

    // -------- //
    // Receiver //
    // -------- //

    task run_receiver();
        uvm_logic_vector_array::sequence_item #(8) packet_item;
        uvm_logic_vector::sequence_item       #(1) error_item;

        forever begin
            // Reset logic
            if (reset_sync.has_been_reset()) begin
                request_queue.delete();
            end

            wait(request_queue.size() < REQUEST_QUEUE_SATURATION_THRESHOLD);

            packet.get_next_item(packet_item);
            error.get_next_item(error_item);

            prepare_requests(packet_item, error_item);

            packet.item_done();
            error.item_done();
        end
    endtask

    function void prepare_requests(uvm_logic_vector_array::sequence_item #(8) packet_item, uvm_logic_vector::sequence_item #(1) error_item);
        uvm_lbus::sequence_item request;
        int unsigned active_segment;
        int unsigned segment_offset = 0;
        int unsigned data_offset = 0;

        try_to_fit_into_previous_request(request, active_segment);

        forever begin
            logic [8-1 : 0] databyte = packet_item.data[data_offset];

            // Create a new request object
            if (request == null) begin
                bit randomize_result;
                request = uvm_lbus::sequence_item::type_id::create("request");
                randomize_result = request.randomize() with { ena == 4'b0; };
                assert(randomize_result)
                else begin
                    `uvm_fatal(this.get_full_name(), "\n\tCannot randomize")
                end

                active_segment = 0;
                segment_offset = 0;
            end

            // Write data
            request.data[128*active_segment + 8*(segment_offset+1)-1 -: 8] = databyte;
            if (segment_offset == 0) begin
                request.ena[active_segment] = 1'b1;
                request.sop[active_segment] = (data_offset == 0) ? 1'b1 : 1'b0;
                request.eop[active_segment] = 1'b0;
            end

            data_offset++;
            if (data_offset != packet_item.data.size()) begin
                // Update logic
                segment_offset++;
                if (segment_offset == 16) begin
                    segment_offset = 0;
                    active_segment++;
                end

                if (active_segment > 3) begin
                    request_queue.push_back(request);
                    request = null;
                end
            end
            else begin
                // Loop exit
                break;
            end
        end

        assert(request != null);

        // Process end of the packet
        request.eop[active_segment] = 1'b1;
        request.err[active_segment] = error_item.data;
        request.mty[4*(active_segment+1)-1 -: 4] = (128/8)-segment_offset-1;
        request_queue.push_back(request);
    endfunction

    function void try_to_fit_into_previous_request(output uvm_lbus::sequence_item request, output int unsigned active_segment);
        uvm_lbus::sequence_item temp_request;
        bit has_sop;
        int unsigned eop_segment;

        // Does a previous request exist?
        if (request_queue.size() == 0) begin
            return;
        end
        temp_request = request_queue[$];

        // Does it already have a sop?
        has_sop = |(temp_request.ena & temp_request.sop);
        if (has_sop) begin
            return;
        end

        // Is there a free segment after the eop?
        for (int unsigned i = 0; i < 4; i++) begin
            if (temp_request.ena[i] & temp_request.eop[i]) begin
                eop_segment = i;
                break;
            end
        end
        if (eop_segment == 3) begin
            return;
        end

        // Successfully found
        request = temp_request;
        active_segment = eop_segment+1;
        // Remove the request from the queue
        request_queue.delete(request_queue.size()-1);
    endfunction

endclass
