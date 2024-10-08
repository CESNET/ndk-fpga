// sequencer.sv: Virtual sequencer
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, EXTENDED_META_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_dropper::virt_sequencer#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, EXTENDED_META_WIDTH))

    uvm_reset::sequencer                                                           m_reset_sqr;
    uvm_logic_vector_array::sequencer#(ITEM_WIDTH)                                 m_mfb_data_sqr;
    uvm_logic_vector::sequencer#(EXTENDED_META_WIDTH)                              m_mfb_meta_sqr;
    uvm_mfb::sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_mfb_rdy_sqr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
