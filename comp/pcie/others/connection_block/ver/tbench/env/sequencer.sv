/*
 * file       : sequencer.sv
 * description: virtual sequencer associate all sequencer together
 * date       : 2020
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * Copyright (C) 2020 CESNET
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef TEST_SEQUENCER_SV_
`define TEST_SEQUENCER_SV_

////////////////////////////////////////////////////////////////////////////////
// vurtual sequencer.
class virtual_sequencer extends uvm_sequencer;
    `uvm_component_utils(env::virtual_sequencer);

    // variables
    packet::sequencer#(ITEM_WIDTH, MFB_META_TX_WIDTH) avalon_rx_sequencer;
    avst_tx::sequencer avalon_tx_sequencer;
    //PTC
    mfb_rx::sequencer #(ITEM_WIDTH, MFB_META_RX_WIDTH) mfb_rx_ptc_sequencer;
    mfb_tx::sequencer mfb_tx_ptc_sequencer;
    //MI
    mfb_rx::sequencer #(ITEM_WIDTH, MFB_META_RX_WIDTH) mfb_rx_mi_sequencer;
    mfb_tx::sequencer mfb_tx_mi_sequencer;

    //functions
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass

`endif
