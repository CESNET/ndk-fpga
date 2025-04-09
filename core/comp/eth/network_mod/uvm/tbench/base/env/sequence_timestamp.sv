// sequence_timestamp.sv: Generates timestamps
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class sequence_timestamp extends uvm_logic_vector::sequence_simple #(64);
    `uvm_object_utils(uvm_network_mod_env::sequence_timestamp)

    localparam int unsigned STEP_MAX = 100;
    localparam int unsigned STEP_MIN = 1;

    // Shared accumulator
    static longint unsigned accumulator = $urandom();

    // Constructor
    function new(string name = "sequence_timestamp");
        super.new(name);
    endfunction

    task body;
        repeat (transaction_count) begin
            req = uvm_logic_vector::sequence_item #(64)::type_id::create("req");
            start_item(req);
            req.data = get_timestamp();
            finish_item(req);
        end
    endtask

    function longint unsigned get_timestamp();
        int unsigned step = $urandom_range(STEP_MAX, STEP_MIN);
        accumulator += step;

        return accumulator;
    endfunction

endclass
