// sequencer.sv: Virtual sequencer
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Mikuláš Brázda <xbrazd21@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer#(ITEM_WIDTH, META_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(virt_sequencer#(ITEM_WIDTH, META_WIDTH))

    uvm_reset::sequencer                m_reset;
    uvm_logic_vector_array_mfb::sequencer_rx #(ITEM_WIDTH, META_WIDTH)    m_mfb_byte_array_scr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
