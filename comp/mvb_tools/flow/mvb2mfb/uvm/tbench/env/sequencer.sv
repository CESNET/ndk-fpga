// sequencer.sv: Virtual sequencer
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer #(MVB_ITEM_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(virt_sequencer #(MVB_ITEM_WIDTH))

    // verilog_lint: waive line-length
    uvm_reset::sequencer                                                                                                m_reset_sqr;
    // verilog_lint: waive line-length
    uvm_logic_vector::sequencer #(MVB_ITEM_WIDTH)                                                                       m_mvb_data_sqr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
