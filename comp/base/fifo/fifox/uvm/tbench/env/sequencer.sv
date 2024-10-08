// sequencer.sv: Virtual sequencer
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class virt_sequencer #(DATA_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_fifox::virt_sequencer #(DATA_WIDTH))

    uvm_reset::sequencer m_reset;

    uvm_logic_vector::sequencer #(DATA_WIDTH)    m_mvb_rx_sqr;
    uvm_mvb::sequencer          #(1, DATA_WIDTH) m_mvb_tx_sqr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
