// data_sequence.sv: Generate data with a stream number stamp
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class data_sequence #(int unsigned MVB_ITEM_WIDTH, int unsigned RX_STREAMS) extends uvm_logic_vector::sequence_simple #(MVB_ITEM_WIDTH);
    `uvm_object_param_utils(test::data_sequence #(MVB_ITEM_WIDTH, RX_STREAMS))
    `m_uvm_get_type_name_func(test::data_sequence)

    // The stream number on which this sequence is running
    int unsigned stream_number;

    // Constructor
    function new(string name = "trim_sequence_length_base");
        super.new(name);

        assert(MVB_ITEM_WIDTH >= $clog2(RX_STREAMS))
        else begin
            `uvm_fatal(get_full_name(), $sformatf("\n\tMVB_ITEM_WIDTH (%0d) cannot be smaller than log2(RX_STREAMS) (%0d)\n", MVB_ITEM_WIDTH, $clog2(RX_STREAMS)))
        end
    endfunction

    task body;
        repeat (transaction_count) begin
            `uvm_do_with(req, {
                req.data[$clog2(RX_STREAMS)-1 -: $clog2(RX_STREAMS)] == stream_number;
            })
        end
    endtask

endclass
