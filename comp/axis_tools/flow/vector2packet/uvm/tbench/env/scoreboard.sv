// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>
// SPDX-License-Identifier: BSD-3-Clause

class scoreboard_cmp #(
    int unsigned TX_ITEMS,
    int unsigned TX_ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_common::comparer_base_ordered#(uvm_axi::sequence_item#(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH));
    `uvm_component_utils(uvm_vector2packet::scoreboard_cmp #(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH))

    // Contructor of scoreboard.
    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        return tr_model.compare(tr_dut);
    endfunction

    function void write_dut(DUT_ITEM tr);
        if (tr.tvalid == 1'b1 && tr.tready == 1'b1) begin
            super.write_dut(tr);
        end
    endfunction
endclass

class scoreboard #(
    int unsigned TX_ITEMS,
    int unsigned TX_ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_scoreboard;
    `uvm_component_utils(uvm_vector2packet::scoreboard #(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH))

    // Transaction comparator
    uvm_vector2packet::scoreboard_cmp #(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH) cmp;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // return 1 when there si no error otherwise 0
    function int unsigned success();
        int unsigned ret = 1;
        ret &= cmp.success();
        return ret;
    endfunction

    // return 1 when waiting for some transactions from DUT
    function int unsigned used();
        int unsigned ret = 0;
        ret |= cmp.used();
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        // Create scoreboard
        cmp = scoreboard_cmp #(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH)::type_id::create("cmp", this);
    endfunction

    function void report_phase(uvm_phase phase);
        string msg = "\n\n\n\t---------------------------------------\n\t----     ";
        if (this.success() && this.used() == 0) begin
            msg = {msg, "VERIFICATION SUCCESS"};
        end else begin
            msg = {msg, "VERIFICATION FAILED"};
        end
        `uvm_info(get_type_name(), {msg, "      ----\n\t---------------------------------------"}, UVM_NONE)
    endfunction
endclass
