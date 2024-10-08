// sequencer.sv: Virtual sequencer
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer#(ITEM_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_discard::virt_sequencer#(ITEM_WIDTH))

    uvm_reset::sequencer                     m_reset;
    uvm_logic_vector::sequencer#(ITEM_WIDTH) m_logic_vector_scr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
