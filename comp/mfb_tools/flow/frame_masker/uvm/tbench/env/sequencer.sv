// sequencer.sv: Virtual sequencer
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kondys <kondys@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(virt_sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))

    uvm_reset::sequencer                                                                                              m_reset_sqr;
    uvm_logic_vector_array::sequencer #(MFB_ITEM_WIDTH)                                                               m_mfb_data_sqr;
    uvm_logic_vector::sequencer       #(MFB_META_WIDTH)                                                               m_mfb_meta_sqr;
    uvm_logic_vector::sequencer       #(1)                                                                            m_mvb_data_sqr;
    uvm_mfb::sequencer                #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) m_mfb_rdy_sqr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
