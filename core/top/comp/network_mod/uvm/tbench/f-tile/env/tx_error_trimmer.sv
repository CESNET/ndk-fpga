// tx_error_trimmer.sv: Trims unused error data on TX side
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class tx_error_trimmer extends uvm_subscriber #(uvm_logic_vector::sequence_item #(6));
    `uvm_component_utils(uvm_network_mod_f_tile_env::tx_error_trimmer)

    localparam int unsigned INPUT_ITEM_WIDTH  = 6;
    localparam int unsigned OUTPUT_ITEM_WIDTH = 1;

    uvm_analysis_port #(uvm_logic_vector::sequence_item #(OUTPUT_ITEM_WIDTH)) analysis_port;

    function new(string name = "tx_error_trimmer", uvm_component parent = null);
        super.new(name, parent);

        analysis_port = new("analysis_port", this);
    endfunction

    function void write(uvm_logic_vector::sequence_item #(INPUT_ITEM_WIDTH) t);
        logic           fcs_error;
        logic [2-1 : 0] error;
        logic [3-1 : 0] status_data;
        uvm_logic_vector::sequence_item #(OUTPUT_ITEM_WIDTH) item;

        { fcs_error, error, status_data } = t.data;
        item = uvm_logic_vector::sequence_item #(OUTPUT_ITEM_WIDTH)::type_id::create("item");
        item.data = fcs_error;

        analysis_port.write(item);
    endfunction

endclass
