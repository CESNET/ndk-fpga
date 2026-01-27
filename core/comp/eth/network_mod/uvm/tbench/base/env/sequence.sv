//-- sequnece.sv: Virtual sequence
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class virt_sequence_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, int unsigned ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(uvm_network_mod_env::virt_sequence_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));
    `uvm_declare_p_sequencer(uvm_network_mod_env::sequencer_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));


    localparam int unsigned RX_MAC_COUNT = 16;

    uvm_sequence#(uvm_reset::sequence_item) eth_rst;
    uvm_sequence#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))  usr_rx_data;
    uvm_sequence#(uvm_logic_vector::sequence_item#(ETH_TX_HDR_WIDTH))  usr_rx_meta;

    protected uvm_common::sequences_cfg_sync#(2) seq_sync_usr_rx;
    protected uvm_common::sequence_cfg_signal seq_sync_end;

    protected uvm_logic_vector_array::config_sequence usr_rx_seq_cfg;

    uvm_network_mod_env::sequence_mac_check_configuration    #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH) m_sequence_mac_check_configuration;
    uvm_network_mod_env::sequence_frame_length_configuration #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH) m_sequence_frame_length_configuration;

    rand int unsigned transactions_approx;
    constraint c_transactions {
        //transactions_approx inside {[30_000:40_000]};
        transactions_approx dist {
                [150:400]  :/ 5,
                [400:1000] :/ 10,
                [1000:2000] :/ 15,
                [2000:4000] :/ 25,
                [4000:10000] :/ 45
            };
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

    function void add_mac_check_addresses(uvm_packet_generators::config_sequence cfg);
        for (int unsigned i = 0; i < RX_MAC_COUNT; i++) begin
            bit            valid;
            bit [48-1 : 0] address;

            { valid, address } = p_sequencer.regmodel.channel[0].rx_mac.mac[i].get();

            if (valid == 1'b1) begin
                cfg.add_mac_address(address);
            end
        end
    endfunction

    virtual task pre_body();
        int unsigned rst = 0;
        uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH)                           lib_usr_rx_data;
        uvm_logic_vector::sequence_simple#(ETH_TX_HDR_WIDTH)                        lib_usr_rx_meta;

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
        lib_usr_rx_data.max_random_count = 20;
        lib_usr_rx_data.min_random_count = 10;
        lib_usr_rx_data.init_sequence();


        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.usr_rx_meta, "", "state", seq_sync_usr_rx.cfg[1]);
        lib_usr_rx_meta = uvm_logic_vector::sequence_simple#(ETH_TX_HDR_WIDTH)::type_id::create("usr_rx_meta" , p_sequencer.usr_rx_meta);
        //lib_usr_rx_meta.config_set();

        // MAC Check configuration
        m_sequence_mac_check_configuration = uvm_network_mod_env::sequence_mac_check_configuration #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_sequence_mac_check_configuration");
        // Frame lengths configuration
        m_sequence_frame_length_configuration = uvm_network_mod_env::sequence_frame_length_configuration #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_sequence_frame_length_configuration");

        usr_rx_data  = lib_usr_rx_data;
        usr_rx_meta  = lib_usr_rx_meta;
    endtask
endclass


class virt_sequence_simple#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, int unsigned ETH_PORT_CHAN[ETH_PORTS], MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(uvm_network_mod_env::virt_sequence_simple#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));
    `uvm_declare_p_sequencer(uvm_network_mod_env::sequencer#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));

    uvm_sequence#(uvm_reset::sequence_item) usr_rst;
    uvm_sequence#(uvm_reset::sequence_item) mi_rst;
    uvm_sequence#(uvm_reset::sequence_item) mi_phy_rst;
    uvm_sequence#(uvm_reset::sequence_item) mi_pmd_rst;

    //uvm_pkg::
    virt_sequence_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH) port[ETH_PORTS];
    protected uvm_logic_vector_array::config_sequence usr_rx_seq_cfg[ETH_PORTS];
    //MI SEQUENCE

    // TSU
    sequence_timestamp tsu;

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

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            port[it] = virt_sequence_port#(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create($sformatf("port_%0d", it), p_sequencer.port[it]);
            port[it].packet_size_set(usr_rx_seq_cfg[it]);
        end

        tsu = sequence_timestamp::type_id::create("tsu");
    endtask

    virtual function void packet_size_set(int unsigned min = 64, int unsigned max = 1500);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            usr_rx_seq_cfg[it] = new($sformatf("usr_rx_seq_cfg_%0d", it));
            usr_rx_seq_cfg[it].array_size_set(min, max);
        end
    endfunction

endclass



