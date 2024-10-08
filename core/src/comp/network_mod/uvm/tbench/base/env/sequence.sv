//-- sequnece.sv: Virtual sequence
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class virt_sequence_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, int unsigned ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(uvm_network_mod_env::virt_sequence_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));
    `uvm_declare_p_sequencer(uvm_network_mod_env::sequencer_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));


    localparam RX_MAC_COUNT = 4;

    uvm_sequence#(uvm_reset::sequence_item) eth_rst;
    uvm_sequence#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))  usr_rx_data;
    uvm_sequence#(uvm_logic_vector::sequence_item#(ETH_TX_HDR_WIDTH))  usr_rx_meta;
    uvm_sequence#(uvm_mfb::sequence_item#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)) usr_tx_data;
    uvm_sequence#(uvm_mvb::sequence_item #(REGIONS, ETH_RX_HDR_WIDTH)) usr_tx_hdr;

    protected uvm_common::sequences_cfg_sync#(2) seq_sync_usr_rx;
    protected uvm_common::sequence_cfg_signal seq_sync_end;

    protected uvm_logic_vector_array::config_sequence usr_rx_seq_cfg;

    rand int unsigned transactions_approx;
    constraint c_transactions {
        //transactions_approx inside {[30_000:40_000]};
        transactions_approx inside {[1000:5000]};
    };

    function new(string name = "uvm_network_mod_env::sequence_simple");
        super.new(name);
        usr_rx_seq_cfg = null;
        seq_sync_end = new();
    endfunction

    function int unsigned rx_transaction_count();
        return seq_sync_usr_rx.data.transactions[0];
    endfunction

    function void packet_size_set(uvm_logic_vector_array::config_sequence usr_rx_seq_cfg);
        this.usr_rx_seq_cfg = usr_rx_seq_cfg;
    endfunction

    virtual task pre_body();
        int unsigned rst = 0;
        uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH)                           lib_usr_rx_data;
        uvm_logic_vector::sequence_simple#(ETH_TX_HDR_WIDTH)                        lib_usr_rx_meta;
        uvm_mfb::sequence_lib_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)  lib_usr_tx_data;
        uvm_mvb::sequence_lib_tx#(REGIONS, ETH_RX_HDR_WIDTH)                        lib_usr_tx_hdr;

        // RESET SEQUENCE
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_rst, "", "state", seq_sync_end);
        if (uvm_config_db#(int unsigned)::get(p_sequencer.eth_rst, "", "rst", rst) == 0 || rst == 0) begin
            eth_rst = uvm_reset::sequence_start::type_id::create("eth_rst", p_sequencer.eth_rst);
            rst = 1;
            uvm_config_db#(int unsigned)::set(p_sequencer.eth_rst, "", "rst", rst);
        end else begin
            eth_rst = uvm_reset::sequence_run::type_id::create("eth_rst", p_sequencer.eth_rst);
        end

        // USR SEQURENCE RX
        seq_sync_usr_rx = uvm_common::sequences_cfg_sync#(2)::type_id::create("seq_sync_usr_rx", m_sequencer);
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.usr_rx_data, "", "state", seq_sync_usr_rx.cfg[0]);
        lib_usr_rx_data = uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH)::type_id::create("usr_rx_data", p_sequencer.usr_rx_data);
        lib_usr_rx_data.max_random_count = 100;
        lib_usr_rx_data.min_random_count = 10;
        lib_usr_rx_data.init_sequence();


        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.usr_rx_meta, "", "state", seq_sync_usr_rx.cfg[1]);
        lib_usr_rx_meta = uvm_logic_vector::sequence_simple#(ETH_TX_HDR_WIDTH)::type_id::create("usr_rx_meta" , p_sequencer.usr_rx_meta);
        //lib_usr_rx_meta.config_set();

        // USR SEQURENCE TX
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.usr_tx_data, "", "state", seq_sync_end);
        lib_usr_tx_data = uvm_mfb::sequence_lib_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)::type_id::create("usr_tx_data", p_sequencer.usr_tx_data);
        lib_usr_tx_data.init_sequence();
        lib_usr_tx_data.max_random_count = 500;
        lib_usr_tx_data.min_random_count = 10;

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.usr_tx_hdr, "", "state", seq_sync_end);
        lib_usr_tx_hdr  = uvm_mvb::sequence_lib_tx#(REGIONS, ETH_RX_HDR_WIDTH)::type_id::create("usr_tx_data", p_sequencer.usr_tx_hdr);
        lib_usr_tx_hdr.init_sequence();
        lib_usr_tx_hdr.max_random_count = 100;
        lib_usr_tx_hdr.min_random_count = 10;

        usr_rx_data  = lib_usr_rx_data;
        usr_rx_meta  = lib_usr_rx_meta;
        usr_tx_data  = lib_usr_tx_data;
        usr_tx_hdr   = lib_usr_tx_hdr;
    endtask

endclass

class virt_sequence_port_stop#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, int unsigned ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends virt_sequence_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_object_param_utils(uvm_network_mod_env::virt_sequence_port_stop#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));
    //`uvm_declare_p_sequencer(uvm_network_mod_env::sequencer_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));

    function new(string name = "uvm_network_mod_env::sequence_simple");
        super.new(name);
    endfunction

endclass

class virt_sequence_simple#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, int unsigned ETH_PORT_CHAN[ETH_PORTS], MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(uvm_network_mod_env::virt_sequence_simple#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));
    `uvm_declare_p_sequencer(uvm_network_mod_env::sequencer#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));

    uvm_sequence#(uvm_reset::sequence_item) usr_rst;
    uvm_sequence#(uvm_reset::sequence_item) mi_rst;
    uvm_sequence#(uvm_reset::sequence_item) mi_phy_rst;
    uvm_sequence#(uvm_reset::sequence_item) mi_pmd_rst;
    uvm_sequence#(uvm_reset::sequence_item) tsu_rst;

    //uvm_pkg::
    virt_sequence_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH) port[ETH_PORTS];
    protected uvm_logic_vector_array::config_sequence usr_rx_seq_cfg[ETH_PORTS];
    //MI SEQUENCE

    //SYNC END
    uvm_common::sequence_cfg_signal seq_sync_end;
    uvm_common::sequence_cfg_signal seq_sync_port_end;

    function new(string name = "uvm_network_mod_env::sequence_simple");
        super.new(name);
        seq_sync_end = new("seq_sync_end");
        seq_sync_port_end = new("seq_sync_port_end");
    endfunction

    virtual task pre_body();
        seq_sync_end.clear();
        seq_sync_port_end.clear();

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.usr_rst, "", "state", seq_sync_end);
        usr_rst    = uvm_reset::sequence_start::type_id::create("usr_rst", p_sequencer.usr_rst);

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.mi_rst, "", "state", seq_sync_end);
        mi_rst     = uvm_reset::sequence_start::type_id::create("mi_rst"    , p_sequencer.mi_rst);

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.mi_phy_rst, "", "state", seq_sync_end);
        mi_phy_rst = uvm_reset::sequence_start::type_id::create("mi_phy_rst", p_sequencer.mi_phy_rst);

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.mi_pmd_rst, "", "state", seq_sync_end);
        mi_pmd_rst = uvm_reset::sequence_start::type_id::create("mi_pmd_rst", p_sequencer.mi_pmd_rst);

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.tsu_rst, "", "state", seq_sync_end);
        tsu_rst    = uvm_reset::sequence_start::type_id::create("tsu_rst"   , p_sequencer.tsu_rst);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            port[it] = virt_sequence_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create($sformatf("port_%0d", it), p_sequencer.port[it]);
            port[it].packet_size_set(usr_rx_seq_cfg[it]);
        end
    endtask

    virtual function void packet_size_set(int unsigned min = 64, int unsigned max = 1500);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            usr_rx_seq_cfg[it] = new($sformatf("usr_rx_seq_cfg_%0d", it));
            usr_rx_seq_cfg[it].array_size_set(min, max);
        end
    endfunction

endclass

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// END SEQUENCES
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
class virt_sequence_stop#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, int unsigned ETH_PORT_CHAN[ETH_PORTS], MI_DATA_WIDTH, MI_ADDR_WIDTH) extends virt_sequence_simple#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_object_param_utils(uvm_network_mod_env::virt_sequence_stop#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));
    `uvm_declare_p_sequencer(uvm_network_mod_env::sequencer#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));

    uvm_sequence#(uvm_reset::sequence_item) usr_rst;
    uvm_sequence#(uvm_reset::sequence_item) mi_rst;
    uvm_sequence#(uvm_reset::sequence_item) mi_phy_rst;
    uvm_sequence#(uvm_reset::sequence_item) mi_pmd_rst;
    uvm_sequence#(uvm_reset::sequence_item) tsu_rst;

    //uvm_pkg::
    virt_sequence_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH) port[ETH_PORTS];
    //MI SEQUENCE

    function new(string name = "uvm_network_mod_env::sequence_simple");
        super.new(name);
    endfunction

    virtual function void stop();
        seq_sync_end.send_stop();
    endfunction

    virtual task pre_body();
        seq_sync_end.clear();

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.usr_rst, "", "state", seq_sync_end);
        usr_rst    = uvm_reset::sequence_run::type_id::create("usr_rst", p_sequencer.usr_rst);

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.mi_rst, "", "state", seq_sync_end);
        mi_rst     = uvm_reset::sequence_run::type_id::create("mi_rst"    , p_sequencer.mi_rst);

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.mi_phy_rst, "", "state", seq_sync_end);
        mi_phy_rst = uvm_reset::sequence_run::type_id::create("mi_phy_rst", p_sequencer.mi_phy_rst);

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.mi_pmd_rst, "", "state", seq_sync_end);
        mi_pmd_rst = uvm_reset::sequence_run::type_id::create("mi_pmd_rst", p_sequencer.mi_pmd_rst);

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.tsu_rst, "", "state", seq_sync_end);
        tsu_rst    = uvm_reset::sequence_run::type_id::create("tsu_rst"   , p_sequencer.tsu_rst);

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.port[it], "", "state", seq_sync_end);
            port[it] = virt_sequence_port_stop#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create($sformatf("port_%0d", it), p_sequencer.port[it]);
        end
    endtask

    virtual task body();
        // RANDOMIZATION
        assert(usr_rst.randomize());
        assert(mi_rst.randomize());
        assert(mi_phy_rst.randomize());
        assert(mi_pmd_rst.randomize());
        assert(tsu_rst.randomize());

        fork
            while (!seq_sync_end.stopped()) begin
                usr_rst.start(p_sequencer.usr_rst, this);
            end
            while (!seq_sync_end.stopped()) begin
                mi_rst.start(p_sequencer.mi_rst, this);
            end
            while (!seq_sync_end.stopped()) begin
                mi_phy_rst.start(p_sequencer.mi_phy_rst, this);
            end
            while (!seq_sync_end.stopped()) begin
                mi_pmd_rst.start(p_sequencer.mi_pmd_rst, this);
            end
            while (!seq_sync_end.stopped()) begin
                tsu_rst.start(p_sequencer.tsu_rst, this);
            end
        join_none

        for (int unsigned it = 0; it <  ETH_PORTS; it++) begin
            fork
                automatic int unsigned index = it;
                begin
                    assert(port[index].randomize());
                    port[index].start(p_sequencer.port[index], this);
                end
            join_none
        end

        while(!seq_sync_end.stopped()) begin
            #(300ns);
        end
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            port[it].wait_for_sequence_state(UVM_FINISHED);
        end

        usr_rst.wait_for_sequence_state(UVM_FINISHED);
        mi_rst.wait_for_sequence_state(UVM_FINISHED);
        mi_phy_rst.wait_for_sequence_state(UVM_FINISHED);
        mi_pmd_rst.wait_for_sequence_state(UVM_FINISHED);
        tsu_rst.wait_for_sequence_state(UVM_FINISHED);
    endtask
endclass

