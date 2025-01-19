// stream_splitter.sv: Splits merged data items to streams
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class stream_splitter #(int unsigned MVB_ITEM_WIDTH, int unsigned RX_STREAMS) extends uvm_subscriber #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH));
    `uvm_component_param_utils(uvm_mvb_merge_streams::stream_splitter #(MVB_ITEM_WIDTH, RX_STREAMS))

    // ------------ //
    // Output ports //
    // ------------ //

    uvm_analysis_port #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH)) analysis_port[RX_STREAMS];

    function new(string name = "stream_splitter", uvm_component parent = null);
        super.new(name, parent);

        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            analysis_port[i] = new($sformatf("analysis_port_%0d", i), this);
        end
    endfunction

    function void write(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH) t);
        int unsigned stream_number = t.data[$clog2(RX_STREAMS)-1 -: $clog2(RX_STREAMS)];

        analysis_port[stream_number].write(t);
    endfunction

endclass
