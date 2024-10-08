/*
 * file       : env.sv
 * description: create enviroment for connection block verification
 * date       : 2020
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * Copyright (C) 2020 CESNET
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef ENV_ENV_SV_
`define ENV_ENV_SV_

///////////////////////////////////////////////////////////////////////////////////////////////
// AVALON rx Transaction. This transaction add some constraints into packet
// transaction.
///////////////////////////////////////////////////////////////////////////////////////////////
class avalon_rx_transaction extends packet::transaction#(ITEM_WIDTH, MFB_META_TX_WIDTH);
        `uvm_object_utils(env::avalon_rx_transaction)

        constraint c_size { meta[127:120] dist { 8'b00001010 := 1, //0A
                                                8'b01001010 := 1, //4A
                                                8'b00001011 := 1, //0B
                                                8'b01001011 := 1, //4B
                                                [0:$]       :/ 4 };};

        function new (string name = "");
            super.new(name);
        endfunction
endclass

///////////////////////////////////////////////////////////////////////////////////////////////
// MFB rx Transaction. This transaction add constraint into mfb_rx
// transaction.
///////////////////////////////////////////////////////////////////////////////////////////////
class mfb_transaction extends mfb_rx::transaction #(ITEM_WIDTH, MFB_META_RX_WIDTH);
        `uvm_object_utils(env::mfb_transaction)

        constraint c_size { meta[29:0] == data.size();};

        function new (string name = "");
            super.new(name);
            this.data_size_max = 128;
            this.data_size_min = 0;
        endfunction
endclass


class mfb_driver_new #(REGIONS, REGIONS_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) extends mfb_rx::driver #(REGIONS, REGIONS_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
   `uvm_component_param_utils(mfb_driver_new#(REGIONS, REGIONS_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void end_of_elaboration_phase(uvm_phase phase);
        m_driver_old.wordDelayEnable_wt  =  5;
        m_driver_old.wordDelayDisable_wt = 95;
        m_driver_old.wordDelayHigh       = 10;
        m_driver_old.wordDelayLow        = 0;
    endfunction
endclass
///////////////////////////////////////////////////////////////////////////////////////////////
// Enviroment for functional verification of connection block
// This enviroment containts two mfb agents and one avalon agent
///////////////////////////////////////////////////////////////////////////////////////////////
class env_base extends uvm_env;
     localparam REGIONS_SIZE = 1;
     localparam BLOCK_SIZE   = 8;
    `uvm_component_utils(env::env_base);

     /////////////////////////////
     // Variables
     //avalon agents
     avst_tx::packet_env#(REGIONS, ITEM_WIDTH, MFB_META_RX_WIDTH) m_avalon_tx_env;
     avst_rx::packet_env#(REGIONS, ITEM_WIDTH, MFB_META_TX_WIDTH) m_avalon_rx_env;
     //PTC mfb agents
     mfb_rx::agent #(REGIONS, REGIONS_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_RX_WIDTH) m_mfb_rx_agent_ptc;
     mfb_tx::agent #(REGIONS, REGIONS_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_TX_WIDTH) m_mfb_tx_agent_ptc;
     //MI32 mfb agents
     mfb_rx::agent #(REGIONS, REGIONS_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_RX_WIDTH) m_mfb_rx_agent_mi;
     mfb_tx::agent #(REGIONS, REGIONS_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_TX_WIDTH) m_mfb_tx_agent_mi;

     // scoreboard and virtual sequencer
     // connect all important things together
     scoreboard             sc;
     virtual_sequencer vir_sqr;

     /////////////////////////////
     // functions
     function new (string name, uvm_component parent);
        super.new(name, parent);
     endfunction

    function void build_phase(uvm_phase phase);
        //change mfb transaction ...
        mfb_rx::transaction #(ITEM_WIDTH, MFB_META_RX_WIDTH)::type_id::set_inst_override(mfb_transaction::get_type(), {this.get_full_name() ,".m_mfb_rx_agent_ptc.*"});
        mfb_rx::transaction #(ITEM_WIDTH, MFB_META_RX_WIDTH)::type_id::set_inst_override(mfb_transaction::get_type(), {this.get_full_name() ,".m_mfb_rx_agent_mi.*"});
        packet::transaction#(ITEM_WIDTH, MFB_META_TX_WIDTH)::type_id::set_type_override(avalon_rx_transaction::get_type());

        mfb_rx::driver#(REGIONS, REGIONS_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_RX_WIDTH)::type_id::set_type_override(mfb_driver_new#(REGIONS, REGIONS_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_RX_WIDTH)::get_type());

        //create agents
        //avalon agents
        m_avalon_tx_env = avst_tx::packet_env#(REGIONS, ITEM_WIDTH, MFB_META_RX_WIDTH)::type_id::create("m_avalon_tx_env", this);
        m_avalon_rx_env = avst_rx::packet_env#(REGIONS, ITEM_WIDTH, MFB_META_TX_WIDTH)::type_id::create("m_avalon_rx_env", this);
        //PTC agents
        m_mfb_rx_agent_ptc = mfb_rx::agent#(REGIONS, REGIONS_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_RX_WIDTH)::type_id::create("m_mfb_rx_agent_ptc", this);
        m_mfb_tx_agent_ptc = mfb_tx::agent#(REGIONS, REGIONS_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_TX_WIDTH)::type_id::create("m_mfb_tx_agent_ptc", this);
        //MI agents
        m_mfb_rx_agent_mi = mfb_rx::agent#(REGIONS, REGIONS_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_RX_WIDTH)::type_id::create("m_mfb_rx_agent_mi", this);
        m_mfb_tx_agent_mi = mfb_tx::agent#(REGIONS, REGIONS_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_TX_WIDTH)::type_id::create("m_mfb_tx_agent_mi", this);

        // create sequencer and scoreboard
        sc = scoreboard::type_id::create("sc", this);
        vir_sqr = virtual_sequencer::type_id::create("vir_sqr", this);
    endfunction

    function void connect_phase(uvm_phase phase);
       // connect agents
       //avalon
       m_avalon_tx_env.analysis_port.connect(sc.analysis_imp_avalon_tx);
       m_avalon_rx_env.analysis_port.connect(sc.analysis_imp_avalon_rx);
       //ptc
       m_mfb_tx_agent_ptc.analysis_port.connect(sc.analysis_imp_mfb_tx_ptc);
       m_mfb_rx_agent_ptc.analysis_port.connect(sc.analysis_imp_mfb_rx_ptc);
       //mi
       m_mfb_tx_agent_mi.analysis_port.connect(sc.analysis_imp_mfb_tx_mi);
       m_mfb_rx_agent_mi.analysis_port.connect(sc.analysis_imp_mfb_rx_mi);

       //get sequencers to virtual sequencer
       vir_sqr.avalon_rx_sequencer  = m_avalon_rx_env.m_sequencer;
       vir_sqr.avalon_tx_sequencer  = m_avalon_tx_env.m_sequencer;
       vir_sqr.mfb_rx_ptc_sequencer = m_mfb_rx_agent_ptc.m_sequencer;
       vir_sqr.mfb_tx_ptc_sequencer = m_mfb_tx_agent_ptc.m_sequencer;
       vir_sqr.mfb_rx_mi_sequencer  = m_mfb_rx_agent_mi.m_sequencer;
       vir_sqr.mfb_tx_mi_sequencer  = m_mfb_tx_agent_mi.m_sequencer;
    endfunction
endclass

`endif
