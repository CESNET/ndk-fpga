// sequencer.sv: Virtual sequencer
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mfb_pipe::virt_sequencer#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    uvm_reset::sequencer                           m_reset;
    uvm_logic_vector_array::sequencer#(ITEM_WIDTH) m_mfb_data_sqr;
    uvm_logic_vector::sequencer #(META_WIDTH)      m_mfb_meta_sqr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
