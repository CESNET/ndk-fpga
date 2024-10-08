// sequence_set.sv Sequence generating user defined MI and data transactions
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_mfb_data #(DATA_WIDTH) extends uvm_sequence #(uvm_logic_vector_array::sequence_item #(DATA_WIDTH));

    `uvm_object_param_utils(uvm_dropper::sequence_mfb_data#(DATA_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence_mfb_data");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------

    // Generates transactions
    task body;
        req = uvm_logic_vector_array::sequence_item#(DATA_WIDTH)::type_id::create("req");

        // Send random data with specific size
        `uvm_do_with(req, {data.size == 137; });
        `uvm_do_with(req, {data.size == 62; });
        `uvm_do_with(req, {data.size == 150; });
        `uvm_do_with(req, {data.size == 512; });

    endtask

endclass

class sequence_meta #(META_WIDTH, EXTENDED_META_WIDTH) extends uvm_sequence #(uvm_logic_vector::sequence_item #(EXTENDED_META_WIDTH));

    `uvm_object_param_utils(uvm_dropper::sequence_meta#(META_WIDTH, EXTENDED_META_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence_meta");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------

    // Generates transactions
    task body;
        logic[META_WIDTH-1 : 0] m_meta;
        logic                   drop;
        req = uvm_logic_vector::sequence_item#(EXTENDED_META_WIDTH)::type_id::create("req");

        // Send random meta with asserted drop signal
        start_item(req);
        void'(std::randomize(m_meta));
        drop   = 1'b1;
        // In the DUT the drop and metadata will be in one signal
        req.data = {drop, m_meta};
        finish_item(req);

        // Send random meta with deasserted drop signal
        start_item(req);
        void'(std::randomize(m_meta));
        drop   = 1'b0;
        // In the DUT the drop and metadata will be in one signal
        req.data = {drop, m_meta};
        finish_item(req);

        // Send random meta with deasserted drop signal
        start_item(req);
        void'(std::randomize(m_meta));
        drop   = 1'b0;
        // In the DUT the drop and metadata will be in one signal
        req.data = {drop, m_meta};
        finish_item(req);

        // Send random meta with asserted drop signal
        start_item(req);
        void'(std::randomize(m_meta));
        drop   = 1'b1;
        // In the DUT the drop and metadata will be in one signal
        req.data = {drop, m_meta};
        finish_item(req);

    endtask

endclass
