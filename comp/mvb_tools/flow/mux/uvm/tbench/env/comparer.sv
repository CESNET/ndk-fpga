//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Oliver Gurka <xgurka00@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class mvb_comparer #(ITEMS, ITEM_WIDTH) extends uvm_common::comparer_ordered #(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH));
    `uvm_component_param_utils(uvm_mvb_mux::mvb_comparer #(ITEMS, ITEM_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction // new

    virtual function void write_dut(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH) tr);
        if (tr.src_rdy == 1 && tr.dst_rdy == 1) begin
            super.write_dut(tr);
        end
    endfunction

endclass
