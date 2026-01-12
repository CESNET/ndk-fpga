//-- sequencer.sv: Virtual sequencer
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequencer#(
    int unsigned DMA_PORTS
) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_ptc::sequencer#(DMA_PORTS))

    uvm_reset::sequencer m_reset;
    uvm_reset::sequencer m_dma_reset;

    uvm_pcie::sequencer m_pcie_rc;
    uvm_dma::sequencer  m_dma[DMA_PORTS];
    //uvm_dma_up::sequencer m_packet;
    //uvm_reset::sequencer  m_reset;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
