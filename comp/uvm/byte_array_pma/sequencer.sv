/*
 * file       : sequencer.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII sequencer
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef PMA_SEQUENCER_SV
`define PMA_SEQUENCER_SV

class sequencer extends uvm_sequencer;

    `uvm_component_param_utils(uvm_byte_array_pma::sequencer)

    uvm_byte_array::sequencer m_packet;

    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
`endif
