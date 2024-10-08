/*
 * file       : sequence.sv
 * description: virtual sequence run on virtual sequencer ....
 * date       : 2020
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * Copyright (C) 2020 CESNET
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef TEST_SEQUENCE_SV_
`define TEST_SEQUENCE_SV_

////////////////////////////////////////////////////////////////////////////////
// virtual sequence which can run on virtual sequencer.
// this sequence is end when
class virtual_sequence extends uvm_sequence;
    `uvm_object_utils(env::virtual_sequence)
    `uvm_declare_p_sequencer(virtual_sequencer);

    //////////////////////////////////
    // variables
    rand int unsigned mvb_rx_count;

    //////////////////////////////////
    // constraints
    constraint s1{
        mvb_rx_count    inside {[10:20]};
    }

    //////////////////////////////////
    // functions
    function new (string name = "");
        super.new(name);
    endfunction

    //////////////////////////////////
    //run sequence on avalon sequencer
    task avalon_rx_sequence();
        packet::sequence_item#(ITEM_WIDTH, MFB_META_TX_WIDTH)  avalon_rx_seq_base;

        //last sequence => waiting for others
        forever begin
            avalon_rx_seq_base = packet::sequence_item#(ITEM_WIDTH, MFB_META_TX_WIDTH)::type_id::create("avalon_rx_seq_base");
            avalon_rx_seq_base.randomize();
            avalon_rx_seq_base.set_starting_phase(get_starting_phase());
            avalon_rx_seq_base.start(p_sequencer.avalon_rx_sequencer);
        end
    endtask

    task avalon_tx_sequence();
       avst_tx::sequence_item avalon_tx_seq;
       forever begin
            avalon_tx_seq = avst_tx::sequence_item::type_id::create("avalon_tx_seq");
            avalon_tx_seq.randomize();
            avalon_tx_seq.set_starting_phase(get_starting_phase());
            avalon_tx_seq.start(p_sequencer.avalon_tx_sequencer);
        end
    endtask

    //////////////////////////////////
    // MFB RX
    task mfb_rx_sequence(mfb_rx::sequencer #(ITEM_WIDTH, MFB_META_RX_WIDTH) sequencer);
        mfb_rx::sequence_lib #(ITEM_WIDTH, MFB_META_RX_WIDTH)  mfb_rx_seq;
        mfb_rx::sequence_item #(ITEM_WIDTH, MFB_META_RX_WIDTH) mfb_rx_seq_base;

        mfb_rx_seq = mfb_rx::sequence_lib #(ITEM_WIDTH, MFB_META_RX_WIDTH)::type_id::create("mfb_rx_seq_lib");
        mfb_rx_seq.min_random_count = 10;
        mfb_rx_seq.max_random_count = 50;
        repeat(mvb_rx_count) begin
            mfb_rx_seq.randomize();
            mfb_rx_seq.set_starting_phase(get_starting_phase());
            mfb_rx_seq.start(sequencer);
        end

        mfb_rx_seq_base = mfb_rx::sequence_item#(ITEM_WIDTH, MFB_META_RX_WIDTH)::type_id::create("mfb_rx_seq_base");
        mfb_rx_seq_base.randomize();
        mfb_rx_seq_base.set_starting_phase(get_starting_phase());
        mfb_rx_seq_base.start(sequencer);
    endtask

    //////////////////////////////////
    // PTC
    /////////////////////////////////
    task mfb_tx_sequence_ptc();
        mfb_tx::sequence_item mfb_tx_ptc_seq;

        forever begin
            mfb_tx_ptc_seq = mfb_tx::sequence_item::type_id::create("mfb_tx_ptc_seq");
            mfb_tx_ptc_seq.ready_one  = 10;
            mfb_tx_ptc_seq.ready_zero = 1;
            mfb_tx_ptc_seq.randomize();
            mfb_tx_ptc_seq.set_starting_phase(get_starting_phase());
            mfb_tx_ptc_seq.start(p_sequencer.mfb_tx_ptc_sequencer);
        end
   endtask

    //////////////////////////////////
    // PTC
    task mfb_tx_sequence_mi();
        mfb_tx::sequence_item mfb_tx_mi_seq;

        forever begin
            mfb_tx_mi_seq = mfb_tx::sequence_item::type_id::create("mfb_tx_mi_seq");
            mfb_tx_mi_seq.randomize();
            mfb_tx_mi_seq.set_starting_phase(get_starting_phase());
            mfb_tx_mi_seq.start(p_sequencer.mfb_tx_mi_sequencer);
        end
    endtask

    //////////////////////////////
    //run all sequences paralelly
    task body;
        fork
            //avalon
            avalon_rx_sequence();
            avalon_tx_sequence();

            //PTC
            mfb_rx_sequence(p_sequencer.mfb_rx_ptc_sequencer);
            mfb_tx_sequence_ptc();

            //MI
            mfb_rx_sequence(p_sequencer.mfb_rx_mi_sequencer);
            mfb_tx_sequence_mi();
        join
    endtask

     `ifndef UVM_POST_VERSION_1_1
        function uvm_phase get_starting_phase();
            return starting_phase;
        endfunction: get_starting_phase

        function void set_starting_phase(uvm_phase phase);
            starting_phase = phase;
        endfunction: set_starting_phase
    `endif
endclass
`endif
