// sequencer.sv: Virtual sequencer
// Copyright (C) 2023-2024 CESNET z. s. p. o.
// Author(s): Oliver Gurka <xgurka0@stud.fit.vutbr.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer#(ITEM_WIDTH, TX_PORTS) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mvb_demux::virt_sequencer#(ITEM_WIDTH, TX_PORTS))

    uvm_reset       ::sequencer                                  m_reset_sqcr;
    uvm_logic_vector::sequencer#(ITEM_WIDTH + $clog2(TX_PORTS))  m_logic_vector_sqcr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
