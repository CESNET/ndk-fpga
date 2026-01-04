// sequencer.sv: Virtual sequencer
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class sequencer extends uvm_sequencer;
    `uvm_component_param_utils(uvm_cq_mfb2axi::sequencer)

    uvm_reset::sequencer m_reset;
    uvm_pcie::sequencer  m_cq;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
