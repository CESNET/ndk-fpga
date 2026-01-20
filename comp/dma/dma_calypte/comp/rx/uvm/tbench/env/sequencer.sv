//-- sequencer.sv: Virtual sequencer
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequencer #(
    int unsigned USR_MFB_ITEM_WIDTH,
    int unsigned CHANNELS
) extends uvm_sequencer;

    `uvm_component_param_utils(uvm_dma_ll::sequencer #(USR_MFB_ITEM_WIDTH, CHANNELS))

    uvm_reset::sequencer                               m_reset_sqcr;
    uvm_dma_ll_rx::sequencer#(USR_MFB_ITEM_WIDTH)      m_usr_mfb_sqcr;
    uvm_dma_ll::regmodel #(CHANNELS)                   m_regmodel_sqcr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
