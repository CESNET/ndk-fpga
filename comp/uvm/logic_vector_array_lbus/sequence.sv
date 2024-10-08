// sequence.sv: LBUS sequences
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// ========= //
// Sequences //
// ========= //

class sequence_tx extends uvm_sequence #(uvm_lbus::sequence_item);
    `uvm_object_utils(uvm_logic_vector_array_lbus::sequence_tx)
    `uvm_declare_p_sequencer(uvm_lbus::sequencer)

    // High-level sequencer
    protected sequencer_tx hl_sequencer;

    // ---------- //
    // Parameters //
    // ---------- //

    int unsigned hl_transaction_count_max = 60;
    int unsigned hl_transaction_count_min = 10;
    rand int unsigned hl_transaction_count;

    constraint c_hl_transaction_count {
        hl_transaction_count inside {[hl_transaction_count_min : hl_transaction_count_max]};
    }

    // Constructor
    function new(string name = "sequence_tx");
        super.new(name);
    endfunction

    task body;
        assert(uvm_config_db #(sequencer_tx)::get(p_sequencer, "", "hl_sequencer", hl_sequencer))
        else begin
            `uvm_fatal(p_sequencer.get_full_name(), "\n\tCannot get a high-level sequencer");
        end

        run_transceiver();
    endtask

    // ----------- //
    // Transceiver //
    // ----------- //

    virtual task run_transceiver();
        // Get first response
        send_empty();
        get_response(rsp);

        while (hl_transaction_count > 0) begin
            bit allowed = can_send_request();

            // Send logic
            if (allowed) begin
                send_prepared_request();
            end
            else begin
                send_empty();
            end

            // Response logic
            get_response(rsp);
        end
    endtask

    virtual function bit can_send_request();
        return (
            rsp.rdy === 1'b1 &&
            hl_sequencer.request_queue.size() > 0
        );
    endfunction

    task send_empty();
        bit randomize_result;
        req = uvm_lbus::sequence_item::type_id::create("req");
        start_item(req);

        randomize_result = req.randomize() with { ena == 4'b0; };
        assert(randomize_result)
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot randomize")
        end

        finish_item(req);
    endtask

    task send_prepared_request();
        bit end_of_packet;
        req = uvm_lbus::sequence_item::type_id::create("req");
        start_item(req);
        req.copy(hl_sequencer.request_queue.pop_front());

        // Keep track of completely sent packets
        end_of_packet = |(req.ena & req.eop);
        if (end_of_packet) begin
            hl_transaction_count--;
        end

        finish_item(req);
    endtask

endclass

class sequence_tx_stop extends sequence_tx;
    `uvm_object_utils(uvm_logic_vector_array_lbus::sequence_tx_stop)

    // ---------- //
    // Parameters //
    // ---------- //

    int unsigned empty_transaction_count_max = 30;
    int unsigned empty_transaction_count_min = 10;
    rand int unsigned empty_transaction_count;

    constraint c_empty_transaction_count {
        empty_transaction_count inside {[empty_transaction_count_min : empty_transaction_count_max]};
    }

    // Constructor
    function new(string name = "sequence_tx_stop");
        super.new(name);
    endfunction

    task run_transceiver();
        repeat (empty_transaction_count) begin
            send_empty();
            // Response logic
            get_response(rsp);
        end
    endtask

endclass

class sequence_tx_bursting extends sequence_tx;
    `uvm_object_utils(uvm_logic_vector_array_lbus::sequence_tx_bursting)

    // ---------- //
    // Parameters //
    // ---------- //

    // Waiting count
    int unsigned waiting_count_max = 30;
    int unsigned waiting_count_min = 10;
    rand int unsigned waiting_count;

    constraint c_waiting_count {
        waiting_count inside {[waiting_count_min : waiting_count_max]};
    }

    // Running count
    int unsigned running_count_max = 30;
    int unsigned running_count_min = 10;
    rand int unsigned running_count;

    constraint c_running_count {
        running_count inside {[running_count_min : running_count_max]};
    }

    // Constructor
    function new(string name = "sequence_tx_bursting");
        super.new(name);
    endfunction

    function bit can_send_request();
        bit allowed = super.can_send_request();
        if (!allowed) begin
            return 0;
        end

        if (waiting_count > 0) begin
            waiting_count--;
            return 0;
        end
        if (running_count > 0) begin
            running_count--;
            return 1;
        end

        waiting_count = $urandom_range(waiting_count_max, waiting_count_min);
        running_count = $urandom_range(running_count_max, running_count_min);
    endfunction

endclass

// ================== //
// Sequence libraries //
// ================== //

class sequence_library_tx extends uvm_sequence_library #(uvm_lbus::sequence_item);
    `uvm_object_utils(uvm_logic_vector_array_lbus::sequence_library_tx)
    `uvm_sequence_library_utils(uvm_logic_vector_array_lbus::sequence_library_tx)

    function new(string name = "sequence_library_tx");
        super.new(name);
        init_sequence_library();

        add_sequence(sequence_tx         ::get_type());
        add_sequence(sequence_tx_stop    ::get_type());
        add_sequence(sequence_tx_bursting::get_type());
    endfunction

endclass

class sequence_library_tx_fullspeed extends sequence_library_tx;
    `uvm_object_utils(uvm_logic_vector_array_lbus::sequence_library_tx_fullspeed)
    `uvm_sequence_library_utils(uvm_logic_vector_array_lbus::sequence_library_tx_fullspeed)

    function new(string name = "sequence_library_tx_fullspeed");
        super.new(name);
        init_sequence_library();

        add_sequence(sequence_tx::get_type());
    endfunction

endclass
