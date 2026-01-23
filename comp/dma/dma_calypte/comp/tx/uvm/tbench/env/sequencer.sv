// sequencer.sv: Virtual sequencer
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Válek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequencer #(
    int unsigned CHANNELS,
    int unsigned DATA_POINTER_WIDTH
) extends uvm_sequencer;

    `uvm_component_param_utils(uvm_tx_dma_calypte::sequencer #(CHANNELS, DATA_POINTER_WIDTH))

    uvm_reset::sequencer                                              m_reset_sqcr;
    uvm_tx_dma_calypte_cq::sequencer #(DATA_POINTER_WIDTH)            m_packet_sqcr [CHANNELS];

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction
endclass
