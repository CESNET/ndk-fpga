//-- sequence.sv: Sequence of logic vector
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Reusable high level sequence. Contains transaction, which has only data part
class sequence_simple #(int unsigned DATA_WIDTH) extends uvm_common::sequence_base #(config_sequence, sequence_item #(DATA_WIDTH));

    `uvm_object_param_utils(uvm_logic_vector::sequence_simple#(DATA_WIDTH));
    `m_uvm_get_type_name_func(uvm_logic_vector::sequence_simple);

    int unsigned transaction_count_min = 10;
    int unsigned transaction_count_max = 1000;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------

    // Generates transactions
    task body;
        int unsigned it;
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        it = 0;
        while(it < transaction_count && (state == null || state.next())) begin

            // Generate random request
            `uvm_do(req)

            it++;
        end
    endtask

endclass

class sequence_endless #(int unsigned DATA_WIDTH) extends uvm_common::sequence_base #(config_sequence, sequence_item #(DATA_WIDTH));
    `uvm_object_param_utils(uvm_logic_vector::sequence_endless#(DATA_WIDTH))
    `m_uvm_get_type_name_func(uvm_logic_vector::sequence_endless);

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------

    // Generates transactions
    task body;
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        while(state == null || state.next()) begin
            // Generate random request
            `uvm_do(req)
        end
    endtask

endclass
