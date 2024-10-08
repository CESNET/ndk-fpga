// sequencer.sv: Virtual sequencer
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W) extends uvm_sequencer;
    `uvm_component_param_utils(virt_sequencer #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W))

    uvm_reset::sequencer                                                                             m_reset_sqr;
    uvm_logic_vector_array::sequencer #(RX_MFB_ITEM_W)                                               m_mfb_data_sqr;
    uvm_logic_vector::sequencer #(USERMETA_W)                                                        m_mfb_meta_sqr;
    uvm_logic_vector::sequencer #(RX_MVB_ITEM_W)                                                     m_mvb_data_sqr;
    uvm_mfb::sequencer #(TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, USERMETA_W) m_mfb_rdy_sqr;
    uvm_mvb::sequencer #(TX_MFB_REGIONS, USERMETA_W)                                                 m_mvb_rdy_sqr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
