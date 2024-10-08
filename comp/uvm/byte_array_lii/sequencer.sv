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

class sequencer #(int unsigned LOGIC_WIDTH) extends uvm_sequencer;

    `uvm_component_param_utils(uvm_byte_array_lii::sequencer #(LOGIC_WIDTH))

    uvm_byte_array::sequencer             m_packet;
    uvm_logic_vector::sequencer#(LOGIC_WIDTH) m_meta;

    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
`endif
