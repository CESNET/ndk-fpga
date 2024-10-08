// sequencer.sv: Virtual sequencer
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_cq_mfb2axi::virt_sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH))

    uvm_reset::sequencer                                                                  m_reset;
    uvm_logic_vector_array::sequencer#(MFB_ITEM_WIDTH)                                    m_logic_vector_array_scr;
    uvm_mfb::sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) m_pcie;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
