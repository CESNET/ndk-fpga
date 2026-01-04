// sequencer.sv: Virtual sequencer
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer extends uvm_sequencer;
    `uvm_component_param_utils(uvm_pcie_cc_mfb2axi::virt_sequencer)

    uvm_reset::sequencer                   m_reset;
    uvm_logic_vector_array::sequencer#(32) m_logic_vector_array_scr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
