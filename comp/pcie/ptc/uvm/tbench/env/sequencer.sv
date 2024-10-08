//-- sequencer.sv: Virtual sequencer
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class virt_sequencer extends uvm_sequencer;

    `uvm_component_utils(uvm_ptc::virt_sequencer)

    uvm_dma_up::sequencer m_packet;
    //uvm_reset::sequencer  m_reset;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
