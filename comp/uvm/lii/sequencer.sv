/*
 * file       : sequencer.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII sequencer
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef LII_SEQUENCER_SV
`define LII_SEQUENCER_SV

class sequencer #(int unsigned DATA_WIDTH, int unsigned META_WIDTH, int unsigned SOF_WIDTH) extends uvm_sequencer #(sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH));

    `uvm_component_param_utils(uvm_lii::sequencer #(DATA_WIDTH, META_WIDTH, SOF_WIDTH))

    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
`endif
