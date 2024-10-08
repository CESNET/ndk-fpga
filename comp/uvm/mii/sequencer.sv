/*
 * file       : sequencer.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: General MII sequencer
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef MII_SEQUENCER_SV
`define MII_SEQUENCER_SV

class sequencer #(int unsigned CHANNELS, int unsigned WIDTH) extends uvm_sequencer #(uvm_mii::sequence_item #(CHANNELS, WIDTH));

    // ------------------------------------------------------------------------
    // Registration of sequencer to databaze
    `uvm_component_param_utils(uvm_mii::sequencer #(CHANNELS, WIDTH))

    // Constructor
    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);

        WHOLE_BYTES : assert((WIDTH & 7) == 0);
    endfunction: new

endclass

`endif
