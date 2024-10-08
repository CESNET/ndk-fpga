//-- sequnece_eth.sv: Virtual sequence
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Reusable high level sequence. Contains transaction, which has only data part
class sequence_logic_vector #(DATA_WIDTH) extends uvm_common::sequence_base #(uvm_logic_vector::config_sequence, uvm_logic_vector::sequence_item #(DATA_WIDTH));
    `uvm_object_param_utils(uvm_network_mod_env::sequence_logic_vector#(DATA_WIDTH))

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
            req = uvm_logic_vector::sequence_item#(DATA_WIDTH)::type_id::create("req", m_sequencer);
            start_item(req);
            if (!req.randomize() with {data dist {0 :/ 9, [1:$] :/ 1};}) begin
                `uvm_warning(m_sequencer.get_full_name(), "\n\tRandomization req failed action");
            end
            finish_item(req);

            it++;
        end
    endtask

endclass

