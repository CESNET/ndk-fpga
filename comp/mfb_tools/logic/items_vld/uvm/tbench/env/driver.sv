// driver.sv
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class driver#(ITEM_WIDTH, META_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_items_valid::driver#(ITEM_WIDTH, META_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH))

    uvm_seq_item_pull_port #(uvm_header_type::sequence_item#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH), uvm_header_type::sequence_item#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH)) seq_item_port_info;

    mailbox#(uvm_header_type::sequence_item#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH))                 frame_export;
    mailbox #(uvm_logic_vector::sequence_item #(META_WIDTH)) logic_vector_export;

    uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)         payload_req;
    uvm_header_type::sequence_item#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) info_req;

    uvm_logic_vector::sequence_item #(META_WIDTH)       meta;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);

        seq_item_port_info   = new("seq_item_port_info", this);

        frame_export        = new(10);
        logic_vector_export = new(10);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);

        forever begin

            seq_item_port_info.get_next_item(info_req);

            meta  = uvm_logic_vector::sequence_item #(META_WIDTH)::type_id::create("meta");
            meta.data[OFFSET_WIDTH-1 : 0]                         = info_req.offset;
            meta.data[OFFSET_WIDTH+LENGTH_WIDTH-1 : OFFSET_WIDTH] = info_req.length;
            meta.data[META_WIDTH-1 : OFFSET_WIDTH+LENGTH_WIDTH]   = info_req.chsum_en;

            frame_export.put(info_req);
            logic_vector_export.put(meta);

            seq_item_port_info.item_done();
        end
    endtask

endclass
