// sequencer.sv
// Copyright (C) 2022-2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequencer #(int unsigned POINTER_WIDTH) extends uvm_sequencer #(sequence_item);
    `uvm_component_param_utils(uvm_tx_dma_calypte_cq::sequencer #(POINTER_WIDTH));

    uvm_reset::sync_terminate                 m_reset_sync;
    uvm_tx_dma_calypte_regs::regmodel_channel #(POINTER_WIDTH) m_regmodel_channel;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void regmodel_set(uvm_tx_dma_calypte_regs::regmodel_channel #(POINTER_WIDTH) regmodel);
        this.m_regmodel_channel = regmodel;
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m_reset_sync = new();
    endfunction
endclass


