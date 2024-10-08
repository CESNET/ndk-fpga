// sequencer.sv: Virtual sequencer
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer#(MI_DATA_WIDTH, MI_ADDRESS_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mi2axi4lite::virt_sequencer#(MI_DATA_WIDTH, MI_ADDRESS_WIDTH))

    uvm_reset::sequencer                                                  m_reset_sqr;
    uvm_mi::sequencer_slave#(MI_DATA_WIDTH, MI_ADDRESS_WIDTH)             m_mi_sqr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
