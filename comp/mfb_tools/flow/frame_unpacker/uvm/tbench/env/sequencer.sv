// sequencer.sv: Virtual sequencer
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, MVB_ITEM_WIDTH, HEADER_SIZE) extends uvm_sequencer;
    `uvm_component_param_utils(virt_sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, MVB_ITEM_WIDTH, HEADER_SIZE))

    uvm_reset::sequencer                                                                          m_reset;
    uvm_logic_vector_array::sequencer #(ITEM_WIDTH)                                               m_byte_array_scr;
    uvm_mfb::sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH+MVB_ITEM_WIDTH) m_mfb;
    uvm_mvb::sequencer #(REGIONS, META_WIDTH+MVB_ITEM_WIDTH)                                      m_mvb_tx;
    uvm_superpacket_header::sequencer #(MVB_ITEM_WIDTH, HEADER_SIZE)                              m_info;
    uvm_superpacket_size::sequencer                                                               m_size;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
