//-- sequnecer.sv: Virtual sequencer
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequencer_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, int unsigned ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_network_mod_env::sequencer_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));

    uvm_reset::sequencer eth_rst;

    uvm_logic_vector_array::sequencer#(ITEM_WIDTH)  usr_rx_data;
    uvm_logic_vector::sequencer#(ETH_TX_HDR_WIDTH)  usr_rx_meta;
    uvm_mfb::sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0) usr_tx_data;
    uvm_mvb::sequencer #(REGIONS, ETH_RX_HDR_WIDTH)                       usr_tx_hdr;

    reg_model_port#(ETH_PORT_CHAN) regmodel;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void set_regmodel(uvm_network_mod_env::reg_model_port#(ETH_PORT_CHAN) regmodel);
        this.regmodel = regmodel;
    endfunction
endclass

class sequencer#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, int unsigned ETH_PORT_CHAN[ETH_PORTS-1:0], MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_network_mod_env::sequencer#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));

    uvm_reset::sequencer usr_rst;
    uvm_reset::sequencer mi_rst;
    uvm_reset::sequencer mi_phy_rst;
    uvm_reset::sequencer mi_pmd_rst;
    uvm_reset::sequencer tsu_rst;
    uvm_network_mod_env::regmodel #(ETH_PORTS, ETH_PORT_CHAN) regmodel;

    sequencer_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH) port[ETH_PORTS];
    // MI PHY

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            port[it] = sequencer_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create($sformatf("port_%0d", it), this);
        end
    endfunction

    function void set_regmodel(uvm_network_mod_env::regmodel #(ETH_PORTS, ETH_PORT_CHAN) regmodel);
        this.regmodel = regmodel;
        for(int unsigned it = 0; it < ETH_PORTS; it++) begin
            port[it].set_regmodel(this.regmodel.port[it]);
        end
    endfunction

endclass
