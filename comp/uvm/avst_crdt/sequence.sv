// sequence.sv: AVST credit control sequence
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// ======= //
// RX side //
// ======= //

virtual class sequence_rx_base #(int unsigned UPDATE_CNT_WIDTH) extends uvm_sequence #(sequence_item #(UPDATE_CNT_WIDTH));
    `uvm_object_param_utils(uvm_avst_crdt::sequence_rx_base #(UPDATE_CNT_WIDTH))

    // --------- //
    // Variables //
    // --------- //

    sequence_item #(UPDATE_CNT_WIDTH) req;

    // Transaction count
    int unsigned max_transaction_count = 100;
    int unsigned min_transaction_count = 10;
    rand int unsigned transaction_count;
    constraint c_transaction_count {transaction_count inside {[min_transaction_count : max_transaction_count]};}

    // Constructor
    function new(string name = "sequence_rx_base");
        super.new(name);
    endfunction

    pure virtual task send_transaction();

    // Generate transactions
    virtual task body;
        repeat (transaction_count) begin
            req = sequence_item #(UPDATE_CNT_WIDTH)::type_id::create("req");
            send_transaction();
        end
    endtask

endclass

class sequence_rx #(int unsigned UPDATE_CNT_WIDTH) extends sequence_rx_base #(UPDATE_CNT_WIDTH);
    `uvm_object_param_utils(uvm_avst_crdt::sequence_rx #(UPDATE_CNT_WIDTH))

    // Constructor
    function new(string name = "sequence_rx");
        super.new(name);
    endfunction

    virtual task send_transaction();
        int unsigned randomize_result;

        start_item(req);

        randomize_result = req.randomize() with {
            init == 1'b0;
        };
        assert(randomize_result)
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot randomize")
        end

        finish_item(req);
        get_response(rsp);
    endtask

endclass

class sequence_rx_hdr extends sequence_rx #(2);
    `uvm_object_utils(uvm_avst_crdt::sequence_rx_hdr)

    // Constructor
    function new(string name = "sequence_rx_hdr");
        super.new(name);
    endfunction

endclass

class sequence_rx_data extends sequence_rx #(4);
    `uvm_object_utils(uvm_avst_crdt::sequence_rx_data)

    // Constructor
    function new(string name = "sequence_rx_data");
        super.new(name);
    endfunction

endclass

class sequence_rx_initializing #(int unsigned UPDATE_CNT_WIDTH) extends sequence_rx_base #(UPDATE_CNT_WIDTH);
    `uvm_object_param_utils(uvm_avst_crdt::sequence_rx_initializing #(UPDATE_CNT_WIDTH))

    // SEPARATION_LENGTH means length of clock cycle separation between the deassertion of the *update and *init signals.
    // https://www.intel.com/content/www/us/en/docs/programmable/683501/24-2-11-3-0/credit-initialization.html
    localparam int unsigned SEPARATION_LENGTH = 2;

    // Constructor
    function new(string name = "sequence_rx_initializing");
        super.new(name);
    endfunction

    virtual task send_transaction();
        int unsigned randomize_result;

        start_item(req);

        randomize_result = req.randomize() with {
            init == 1'b1;
        };
        assert(randomize_result)
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot randomize")
        end

        finish_item(req);
        get_response(rsp);
    endtask

    virtual task send_separation_transaction();
        int unsigned randomize_result;

        start_item(req);

        randomize_result = req.randomize() with {
            init   == 1'b1;
            update == 1'b0;
        };
        assert(randomize_result)
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot randomize")
        end

        finish_item(req);
        get_response(rsp);
    endtask

    // Generate transactions
    virtual task body;
        repeat (transaction_count-SEPARATION_LENGTH) begin
            req = sequence_item #(UPDATE_CNT_WIDTH)::type_id::create("req");
            send_transaction();
        end

        repeat (SEPARATION_LENGTH) begin
            req = sequence_item #(UPDATE_CNT_WIDTH)::type_id::create("req");
            send_separation_transaction();
        end
    endtask

endclass

class sequence_rx_initializing_hdr extends sequence_rx_initializing #(2);
    `uvm_object_utils(uvm_avst_crdt::sequence_rx_initializing_hdr)

    // Constructor
    function new(string name = "sequence_rx_initializing_hdr");
        super.new(name);
    endfunction

endclass

class sequence_rx_initializing_data extends sequence_rx_initializing #(4);
    `uvm_object_utils(uvm_avst_crdt::sequence_rx_initializing_data)

    // Constructor
    function new(string name = "sequence_rx_initializing_data");
        super.new(name);
    endfunction

endclass

// ======= //
// TX side //
// ======= //

class sequence_tx_ack #(int unsigned UPDATE_CNT_WIDTH) extends uvm_sequence #(sequence_item #(UPDATE_CNT_WIDTH));
    `uvm_object_param_utils(uvm_avst_crdt::sequence_tx_ack #(UPDATE_CNT_WIDTH))

    // Constructor
    function new(string name = "sequence_tx_ack");
        super.new(name);
    endfunction

    virtual task send_empty_transaction();
        int unsigned randomize_result;

        start_item(req);

        randomize_result = req.randomize() with {
            init_ack == 1'b0;
        };
        assert(randomize_result)
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot randomize")
        end

        finish_item(req);
        get_response(rsp);
    endtask

    virtual task send_transaction();
        int unsigned randomize_result;

        start_item(req);

        randomize_result = req.randomize() with {
            init_ack == 1'b1;
        };
        assert(randomize_result)
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot randomize")
        end

        finish_item(req);
        get_response(rsp);
    endtask

    // Generate transactions
    virtual task body;
        do begin
            req = sequence_item #(UPDATE_CNT_WIDTH)::type_id::create("req");
            send_empty_transaction();
        end while(rsp.init !== 1'b1);

        req = sequence_item #(UPDATE_CNT_WIDTH)::type_id::create("req");
        send_transaction();
    endtask

endclass

class sequence_tx_ack_hdr extends sequence_tx_ack #(2);
    `uvm_object_utils(uvm_avst_crdt::sequence_tx_ack_hdr)

    // Constructor
    function new(string name = "sequence_tx_ack_hdr");
        super.new(name);
    endfunction

endclass

class sequence_tx_ack_data extends sequence_tx_ack #(4);
    `uvm_object_utils(uvm_avst_crdt::sequence_tx_ack_data)

    // Constructor
    function new(string name = "sequence_tx_ack_data");
        super.new(name);
    endfunction

endclass
