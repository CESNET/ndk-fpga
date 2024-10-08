/*
 * file       : sequencer.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: size_gen sequencer
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class sequencer #(int unsigned ITEM_WIDTH) extends uvm_sequencer #(sequence_item #(ITEM_WIDTH));
    `uvm_component_utils(uvm_logic_vector_array::sequencer #(ITEM_WIDTH))

    uvm_reset::sync_terminate reset_sync;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        reset_sync = new();
    endfunction
endclass
