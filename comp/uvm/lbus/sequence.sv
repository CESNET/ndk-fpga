// sequence.sv: LBUS sequences
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// ========= //
// Sequences //
// ========= //

class sequence_rx extends uvm_common::sequence_base #(config_sequence, sequence_item);
    `uvm_object_utils(uvm_lbus::sequence_rx)

    // Ready utils
    uvm_common::rand_rdy rdy;

    // ---------- //
    // Parameters //
    // ---------- //

    int unsigned transaction_count_max = 100;
    int unsigned transaction_count_min = 10;
    rand int unsigned transaction_count;

    constraint c_transaction_count { transaction_count inside {[transaction_count_min : transaction_count_max]}; }

    // Constructor
    function new(string name = "sequence_rx");
        super.new(name);

        rdy = new();
    endfunction

    virtual task send_transaction();
        bit randomize_result = 1;
        start_item(req);

        randomize_result &= rdy.randomize();
        randomize_result &= req.randomize() with { rdy == rdy.m_value; };

        assert(randomize_result)
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot randomize")
        end

        finish_item(req);
    endtask

    virtual task pre_body();
        rdy.bound_set(cfg.rdy_probability_min, cfg.rdy_probability_max);
    endtask

    // Generate transactions
    virtual task body;
        uvm_common::sequence_cfg state;
        assert(uvm_config_db #(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state));

        repeat (transaction_count) begin
            if (state != null) begin
                if (!state.next()) begin
                    break;
                end
            end

            req = sequence_item::type_id::create("req");
            send_transaction();
        end
    endtask

endclass

class sequence_rx_stop extends sequence_rx;
    `uvm_object_utils(uvm_lbus::sequence_rx_stop)

    // Constructor
    function new(string name = "sequence_rx_stop");
        super.new(name);
    endfunction

    virtual task send_transaction();
        bit randomize_result;
        start_item(req);

        randomize_result = req.randomize() with { rdy == 1'b0; };
        assert(randomize_result)
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot randomize")
        end

        finish_item(req);
    endtask

endclass

class sequence_rx_fullspeed extends sequence_rx;
    `uvm_object_utils(uvm_lbus::sequence_rx_fullspeed)

    // Constructor
    function new(string name = "sequence_rx_fullspeed");
        super.new(name);
    endfunction

    virtual task send_transaction();
        bit randomize_result;
        start_item(req);

        randomize_result = req.randomize() with { rdy == 1'b1; };
        assert(randomize_result)
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot randomize")
        end

        finish_item(req);
    endtask

endclass

// ================== //
// Sequence libraries //
// ================== //

class sequence_library_rx extends uvm_common::sequence_library #(config_sequence, sequence_item);
    `uvm_object_utils(uvm_lbus::sequence_library_rx)
    `uvm_sequence_library_utils(uvm_lbus::sequence_library_rx)

    // Constructor
    function new(string name = "sequence_library_rx");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        add_sequence(sequence_rx          ::get_type());
        add_sequence(sequence_rx_stop     ::get_type());
        add_sequence(sequence_rx_fullspeed::get_type());
    endfunction

endclass

class sequence_library_rx_fullspeed extends sequence_library_rx;
    `uvm_object_utils(uvm_lbus::sequence_library_rx_fullspeed)
    `uvm_sequence_library_utils(uvm_lbus::sequence_library_rx_fullspeed)

    // Constructor
    function new(string name = "sequence_library_rx_fullspeed");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        add_sequence(sequence_rx_fullspeed::get_type());
    endfunction

endclass
