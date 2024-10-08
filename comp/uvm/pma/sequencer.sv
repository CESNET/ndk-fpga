/*
 * file       : sequencer.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: PMA sequencer
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef PMA_SEQUENCER_SV
`define PMA_SEQUENCER_SV

class sequencer #(int unsigned DATA_WIDTH) extends uvm_sequencer #(sequence_item #(DATA_WIDTH));

    `uvm_component_param_utils(uvm_pma::sequencer #(DATA_WIDTH))

    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction: new

endclass
`endif
