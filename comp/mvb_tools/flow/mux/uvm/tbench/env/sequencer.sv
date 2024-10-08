// sequencer.sv: Virtual sequencer
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer#(ITEM_WIDTH, RX_MVB_CNT) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mvb_mux::virt_sequencer#(ITEM_WIDTH, RX_MVB_CNT))

    uvm_reset::sequencer                     m_reset;
    uvm_logic_vector::sequencer#(ITEM_WIDTH) m_logic_vector_scr[RX_MVB_CNT - 1 : 0];
    uvm_logic_vector::sequencer#($clog2(RX_MVB_CNT)) m_logic_vector_sel_scr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
