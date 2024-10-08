// sequencer.sv: Virtual sequencer
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer#(ITEMS, LUT_WIDTH, REG_DEPTH, SLICE_WIDTH, SW_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_lookup_table::virt_sequencer#(ITEMS, LUT_WIDTH, REG_DEPTH, SLICE_WIDTH, SW_WIDTH))

    uvm_reset::sequencer                                m_reset_sqr;
    uvm_logic_vector::sequencer#(REG_DEPTH-SLICE_WIDTH) m_mvb_data_sqr;
    uvm_mi::sequencer_slave#(SW_WIDTH, REG_DEPTH, 0)    m_mi_sqr;
    uvm_mvb::sequencer #(ITEMS, LUT_WIDTH)              m_mvb_rdy_sqr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
