
/*
 * file       : sequencer.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: High level Byte array - MII sequencer
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef BYTE_MII_SEQUENCER_SV
`define BYTE_MII_SEQUENCER_SV

class sequencer extends uvm_sequencer;
    `uvm_component_param_utils(uvm_byte_array_mii::sequencer)

    uvm_byte_array::sequencer byte_array_sequencer;

    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass

`endif
