// coverage_model.sv: Coverage model for the frame-trimming functionality
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class coverage_model #(int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned LEN_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_mfb_frame_trimmer::coverage_model #(BLOCK_SIZE, ITEM_WIDTH, LEN_WIDTH))

    localparam int unsigned MIN_DATA_LENGTH = 64;
    localparam int unsigned MAX_DATA_LENGTH = (2**LEN_WIDTH)-1;
    localparam int unsigned MIN_TRIM_LENGTH = (BLOCK_SIZE*ITEM_WIDTH)-(ITEM_WIDTH-1);

    // ------ //
    // Inputs //
    // ------ //

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)) in_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(1+LEN_WIDTH))      in_trim;

    // ----------- //
    // Covergroups //
    // ----------- //

    covergroup data_covergroup(string name = "data_covergroup") with function sample(int unsigned data_size);
        option.name = name;
        option.per_instance = 1;

        // =========== //
        // Coverpoints //
        // =========== //

        data_length : coverpoint data_size
        {
            bins min       = { MIN_DATA_LENGTH };
            bins max       = { MAX_DATA_LENGTH };
            bins other[15] = { [MIN_DATA_LENGTH+1 : MAX_DATA_LENGTH-1] };
        }
    endgroup

    covergroup trim_covergroup(string name = "trim_covergroup") with function sample(logic trim_en, logic [LEN_WIDTH-1 : 0] trim_len, bit is_trim_nop);
        option.name = name;
        option.per_instance = 1;

        // =========== //
        // Coverpoints //
        // =========== //

        // TRIM mode
        trim_mode : coverpoint trim_en
        {
            bins on  = { 1'b1 };
            bins off = { 1'b0 };
        }

        // TRIM length
        trim_length : coverpoint trim_len iff (trim_en === 1'b1)
        {
            bins min       = { MIN_TRIM_LENGTH };
            bins max       = { MAX_DATA_LENGTH };
            bins other[10] = { [MIN_TRIM_LENGTH+1 : MAX_DATA_LENGTH-1] };
        }

        // TRIM length = original frame length
        trim_nop : coverpoint is_trim_nop iff (trim_en === 1'b1)
        {
            bins nop   = { 1'b1 };
            bins other = default;
        }
    endgroup

    function new(string name = "coverage_model", uvm_component parent = null);
        super.new(name, parent);

        in_data = new("in_data", this);
        in_trim = new("in_trim", this);

        data_covergroup = new("data_covergroup");
        trim_covergroup = new("trim_covergroup");
    endfunction

    task run_phase(uvm_phase phase);
        uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)  in_data_item;
        uvm_logic_vector::sequence_item       #(1+LEN_WIDTH) in_trim_item;

        int unsigned            data_size;
        logic                   trim_en;
        logic [LEN_WIDTH-1 : 0] trim_len;
        bit                     is_trim_nop;

        forever begin
            in_data.get(in_data_item);
            in_trim.get(in_trim_item);

            data_size = in_data_item.size();

            trim_len    = in_trim_item.data[LEN_WIDTH-1 -: LEN_WIDTH];
            trim_en     = in_trim_item.data[1+LEN_WIDTH-1 -: 1];
            is_trim_nop = (trim_len === data_size);

            data_covergroup.sample(data_size);
            trim_covergroup.sample(trim_en, trim_len, is_trim_nop);
        end
    endtask

endclass
