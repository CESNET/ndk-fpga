// virtual_sequencer.sv: Virtual sequencer for packet_delayer
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequencer #(
    int unsigned ITEM_WIDTH,
    int unsigned EXTENDED_META_WIDTH
) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_packet_delayer::virtual_sequencer #(ITEM_WIDTH, EXTENDED_META_WIDTH))

    uvm_reset::sequencer                               m_reset_sqr;
    uvm_reset::sequencer                               m_time_reset_sqr;
    uvm_logic_vector_array::sequencer #(ITEM_WIDTH)    m_mfb_data_sqr;
    uvm_logic_vector::sequencer #(EXTENDED_META_WIDTH) m_mfb_meta_sqr;

    function new(string name = "virtual_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
