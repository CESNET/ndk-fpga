/*
 * file       : sequencer.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: RESET sequence item
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequencer #(int unsigned SEGMENTS) extends uvm_sequencer #(sequence_item #(SEGMENTS));
    `uvm_component_param_utils(uvm_intel_mac_seg::sequencer #(SEGMENTS))

    uvm_reset::sync_terminate reset_sync;

    // Constructor
    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
        reset_sync = new();
    endfunction: new

endclass

