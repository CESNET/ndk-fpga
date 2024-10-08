//-- sequencer.sv: Virtual sequencer
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mtc::sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    localparam CC_MFB_META_WIDTH = sv_pcie_meta_pack::PCIE_CC_META_WIDTH;

    uvm_reset::sequencer                                                                                  m_reset;
    uvm_pcie_hdr::sequencer                                                                               m_packet;
    uvm_mfb::sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, CC_MFB_META_WIDTH) m_pcie;
    uvm_mi::sequencer_master#(MI_DATA_WIDTH, MI_ADDR_WIDTH)                                               m_mi_sqr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
