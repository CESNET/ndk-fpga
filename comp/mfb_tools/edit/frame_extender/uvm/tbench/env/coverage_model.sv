// coverage_model.sv: Coverage model for the frame-extending functionality
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class coverage_model #(int unsigned MFB_BLOCK_SIZE, int unsigned PKT_MTU, int unsigned EXTENSION_ITEM_WIDTH) extends uvm_subscriber #(uvm_logic_vector::sequence_item #(EXTENSION_ITEM_WIDTH));
    `uvm_component_param_utils(uvm_mfb_frame_extender::coverage_model #(MFB_BLOCK_SIZE, PKT_MTU, EXTENSION_ITEM_WIDTH))

    localparam int unsigned MAX_DATA_LENGTH = PKT_MTU;
    localparam int unsigned MIN_DATA_LENGTH = 64;

    localparam int unsigned MAX_EXTENSION_ONLY_LENGTH = MAX_DATA_LENGTH - (MAX_DATA_LENGTH % MFB_BLOCK_SIZE); // The closest value divisible by MFB_BLOCK_SIZE and less than or equal to MAX_DATA_LENGTH
    localparam int unsigned MAX_EXTENSION_LENGTH      = (MAX_DATA_LENGTH-MIN_DATA_LENGTH) - ((MAX_DATA_LENGTH-MIN_DATA_LENGTH) % MFB_BLOCK_SIZE); // The closest value divisible by MFB_BLOCK_SIZE and less than or equal to (MAX_DATA_LENGTH-MIN_DATA_LENGTH)
    localparam int unsigned MIN_EXTENSION_LENGTH      = 60 - (60 % MFB_BLOCK_SIZE) + MFB_BLOCK_SIZE; // The closest value divisible by MFB_BLOCK_SIZE and greater than or equal to 60

    // ----------- //
    // Covergroups //
    // ----------- //

    covergroup extension_covergroup(string name = "extension_covergroup") with function sample(bit ext_en, bit ext_only, int unsigned ext_size, int unsigned frame_length);
        option.name = name;
        option.per_instance = 1;

        // =========== //
        // Coverpoints //
        // =========== //

        // EXTENSION mode
        extension_mode : coverpoint { ext_en, ext_only }
        {
            bins ext  = { 2'b10 };
            bins only = { 2'b11 };
            bins off  = { 2'b00, 2'b01 };
        }

        // EXTENSION size
        extension_size : coverpoint ext_size iff ({ ext_en, ext_only } === 2'b10)
        {
            bins min  = { MIN_EXTENSION_LENGTH };
            bins max  = { MAX_EXTENSION_LENGTH };
            bins other[10] = { [MIN_EXTENSION_LENGTH+1 : MAX_EXTENSION_LENGTH-1] };
        }

        // EXTENSION ONLY size
        extension_only_size : coverpoint ext_size iff ({ ext_en, ext_only } === 2'b11)
        {
            bins min  = { MIN_EXTENSION_LENGTH };
            bins max  = { MAX_EXTENSION_ONLY_LENGTH };
            bins other[10] = { [MIN_EXTENSION_LENGTH+1 : MAX_EXTENSION_ONLY_LENGTH-1] };
        }

        // DATA size
        data_size : coverpoint frame_length iff ({ ext_en, ext_only } !== 2'b11)
        {
            bins min  = { MIN_DATA_LENGTH };
            bins max  = { MAX_DATA_LENGTH };
            bins other[10] = { [MIN_DATA_LENGTH+1 : MAX_DATA_LENGTH-1] };
        }

        // DATA size per EXTENSION mode
        extension_mode_x_data_size : cross extension_mode, data_size
        {
            ignore_bins only_mode = binsof(extension_mode) intersect { 2'b11 };
            ignore_bins ext_mode_x_max_size = binsof(extension_mode) intersect { 2'b10 } && binsof(data_size) intersect { MAX_DATA_LENGTH };
        }
    endgroup

    function new(string name = "coverage_model", uvm_component parent = null);
        super.new(name, parent);

        extension_covergroup = new({ get_full_name(), ".", "extension_covergroup" });
    endfunction

    function void write(uvm_logic_vector::sequence_item #(EXTENSION_ITEM_WIDTH) t);
        bit          ext_en;
        bit          ext_only;
        int unsigned ext_size;
        int unsigned frame_length;

        ext_en       = t.data[1                                      -1 -: 1];
        ext_only     = t.data[1+1                                    -1 -: 1];
        ext_size     = t.data[$clog2(PKT_MTU+1)+1+1                  -1 -: $clog2(PKT_MTU+1)];
        frame_length = t.data[$clog2(PKT_MTU+1)+$clog2(PKT_MTU+1)+1+1-1 -: $clog2(PKT_MTU+1)];

        extension_covergroup.sample(ext_en, ext_only, ext_size, frame_length);
    endfunction

endclass
