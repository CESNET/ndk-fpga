// tx_error_expander.sv: Expands error bit data on TX side
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class tx_error_expander extends uvm_subscriber #(uvm_logic_vector::sequence_item #(1));
    `uvm_component_utils(uvm_network_mod_cmac_env::tx_error_expander)

    localparam int unsigned INPUT_ITEM_WIDTH  = 1;
    localparam int unsigned OUTPUT_ITEM_WIDTH = 6;

    uvm_analysis_port #(uvm_logic_vector::sequence_item #(OUTPUT_ITEM_WIDTH)) analysis_port;

    // Constructor
    function new(string name = "tx_error_expander", uvm_component parent = null);
        super.new(name, parent);
        analysis_port = new("analysis_port", this);
    endfunction

    function void write(uvm_logic_vector::sequence_item #(INPUT_ITEM_WIDTH) t);
        uvm_logic_vector::sequence_item #(OUTPUT_ITEM_WIDTH)
            item = uvm_logic_vector::sequence_item #(OUTPUT_ITEM_WIDTH)::type_id::create(
            "item"
        );

        item.data = {OUTPUT_ITEM_WIDTH{t.data}};

        analysis_port.write(item);
    endfunction

endclass
