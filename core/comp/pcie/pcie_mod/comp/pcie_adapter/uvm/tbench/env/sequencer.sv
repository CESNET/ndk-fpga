// sequencer.sv: Virtual sequencer
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class sequencer extends uvm_sequencer;
    `uvm_component_param_utils(uvm_pcie_adapter::sequencer)

    // Reset sequencer
    uvm_reset::sequencer m_reset;
    //PCIE
    uvm_pcie::sequencer m_pcie_cq;
    uvm_pcie::sequencer m_pcie_rc;
    // TODO: CRDT
    // PCIE INTEL CREDITD
    uvm_crdt::sequencer m_crdt_up_sqr;
    uvm_crdt::sequencer m_crdt_down_sqr;

    // MFB
    uvm_pcie::sequencer m_mfb_cc;
    uvm_pcie::sequencer m_mfb_rq;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
