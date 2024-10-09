// sequence.sv: Virtual sequences
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class virt_sequence_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, int unsigned ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_network_mod_env::virt_sequence_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_object_param_utils(uvm_network_mod_e_tile_env::virt_sequence_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH))
    `uvm_declare_p_sequencer(uvm_network_mod_e_tile_env::sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH))

    uvm_sequence #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)) eth_rx_data;
    uvm_sequence #(uvm_logic_vector::sequence_item #(6))                eth_rx_meta;
    uvm_sequence #(uvm_avst::sequence_item #(ETH_PORT_CHAN, 1, REGION_SIZE * BLOCK_SIZE, ITEM_WIDTH, 1)) eth_tx;

    protected uvm_common::sequences_cfg_sync#(2) seq_sync_eth_rx;

    protected uvm_logic_vector_array::config_sequence eth_rx_seq_cfg;

    function new(string name = "virt_sequence_port");
        super.new(name);
        eth_rx_seq_cfg = null;
    endfunction

    function int unsigned rx_transaction_count();
        return super.rx_transaction_count() + seq_sync_eth_rx.data.transactions[0];
    endfunction

    function void packet_size_set(uvm_logic_vector_array::config_sequence usr_rx_seq_cfg, uvm_logic_vector_array::config_sequence eth_rx_seq_cfg);
        super.packet_size_set(usr_rx_seq_cfg);
        this.eth_rx_seq_cfg = eth_rx_seq_cfg;
    endfunction

    task pre_body();
        uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH)                           lib_eth_rx_data;
        //uvm_logic_vector::sequence_simple#(6)                                       lib_eth_rx_meta;
        uvm_avst::sequence_lib_tx#(ETH_PORT_CHAN, 1, REGION_SIZE * BLOCK_SIZE, ITEM_WIDTH,  1)  lib_eth_tx;

        super.pre_body();

        // ETH SEQURENCE RX
        seq_sync_eth_rx = uvm_common::sequences_cfg_sync#(2)::type_id::create("seq_sync_eth_rx", m_sequencer);
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_rx_data, "", "state", seq_sync_eth_rx.cfg[0]);
        lib_eth_rx_data = uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH)::type_id::create("eth_rx_data", p_sequencer.eth_rx_data);
        lib_eth_rx_data.max_random_count = 100;
        lib_eth_rx_data.min_random_count = 10;
        lib_eth_rx_data.init_sequence();

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_rx_meta, "", "state", seq_sync_eth_rx.cfg[1]);
        //lib_eth_rx_meta = //uvm_logic_vector::sequence_simple#(6)::type_id::create("eth_rx_meta", p_sequencer.eth_rx_meta);
        eth_rx_meta = uvm_network_mod_env::sequence_logic_vector#(6)::type_id::create("eth_rx_meta", p_sequencer.eth_rx_meta);
        //lib_eth_rx_meta.config_set();

        // ETH SEQURENCE TX
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_tx, "", "state", seq_sync_end);
        lib_eth_tx = uvm_avst::sequence_lib_tx#(ETH_PORT_CHAN, 1, REGION_SIZE * BLOCK_SIZE, ITEM_WIDTH,  1)::type_id::create("eth_tx", p_sequencer.eth_tx);
        lib_eth_tx.init_sequence();
        lib_eth_tx.max_random_count = 100;
        lib_eth_tx.min_random_count = 10;

        eth_rx_data  = lib_eth_rx_data;
        //eth_rx_meta  = lib_eth_rx_meta;
        eth_tx       = lib_eth_tx;
    endtask

    task body();
        uvm_status_e   status;
        uvm_reg_data_t data;
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end
        seq_sync_end.clear();

        fork
            while (!seq_sync_end.stopped()) begin
                assert(eth_rst.randomize());
                eth_rst.start(p_sequencer.eth_rst);
            end
        join_none

        #(400ns);

        for (int unsigned it = 0; it < ETH_PORT_CHAN; it++) begin
            fork
                p_sequencer.regmodel.channel[it].rx_mac.base.enable.write(status, 1'h1);
                p_sequencer.regmodel.channel[it].tx_mac.enable.write(status, 1'h1);
            join;

            fork
                p_sequencer.regmodel.channel[it].rx_mac.base.enable.read(status, data);
                p_sequencer.regmodel.channel[it].tx_mac.enable.read(status, data);
            join;
        end

        fork
            while (!seq_sync_usr_rx.cfg[0].stopped()) begin
                assert(usr_rx_data.randomize());
                usr_rx_data.start(p_sequencer.usr_rx_data);
            end
            while (!seq_sync_usr_rx.cfg[1].stopped()) begin
                assert(usr_rx_meta.randomize());
                usr_rx_meta.start(p_sequencer.usr_rx_meta);
            end
            while (!seq_sync_end.stopped()) begin
                assert(usr_tx_data.randomize());
                usr_tx_data.start(p_sequencer.usr_tx_data);
            end
            while (!seq_sync_end.stopped()) begin
                assert(usr_tx_hdr.randomize());
                usr_tx_hdr.start(p_sequencer.usr_tx_hdr);
            end

            while (!seq_sync_eth_rx.cfg[0].stopped()) begin
                assert(eth_rx_data.randomize());
                eth_rx_data.start(p_sequencer.eth_rx_data);
            end
            while (!seq_sync_eth_rx.cfg[1].stopped()) begin
                assert(eth_rx_meta.randomize());
                eth_rx_meta.start(p_sequencer.eth_rx_meta);
            end
            while (!seq_sync_end.stopped()) begin
                assert(eth_tx.randomize());
                eth_tx.start(p_sequencer.eth_tx);
            end
        join_none

        while ((state == null || !state.stopped()) &&
               (this.rx_transaction_count() < transactions_approx)
           ) begin
            #(300ns);
        end
        seq_sync_usr_rx.send_stop();
        seq_sync_eth_rx.send_stop();

        //READ STATISTIC
        for (int unsigned it = 0; it < ETH_PORT_CHAN; it++) begin
            uvm_network_mod_env::read_rx_counters#(RX_MAC_COUNT) rx_stats;
            uvm_network_mod_env::read_tx_counters                tx_stats;

            rx_stats = uvm_network_mod_env::read_rx_counters#(RX_MAC_COUNT)::type_id::create("rx_stats", m_sequencer);
            rx_stats.set_regmodel(p_sequencer.regmodel.channel[it].rx_mac);
            tx_stats = uvm_network_mod_env::read_tx_counters::type_id::create("tx_stats", m_sequencer);
            tx_stats.set_regmodel(p_sequencer.regmodel.channel[it].tx_mac);

            fork
                rx_stats.start(null);
                tx_stats.start(null);
            join
 
            `uvm_info(this.get_full_name(),
                $sformatf("RX channel %s base [%0d]\n\tSTATS trfc %0d cfc %0d dfc %0d bodfc %0d oroc %0d\n", m_sequencer.get_full_name(), it, rx_stats.trfc, rx_stats.cfc, rx_stats.dfc, rx_stats.bodfc, rx_stats.oroc),
                UVM_LOW);
           `uvm_info(this.get_full_name(),
                $sformatf("RX channel %s rfc  [%0d]\n\tcrc_err %0d\n\tover_mtu_addr %0d\n\t below_min_addr %0d\n\tbcast_frames_addr %0d\n\tmcast_frames_addr %0d\n\tfragment_frames_addr %0d\n\tjabber_frames_addr %0d\n\ttrans_octets_addr %0d\n\tframes_64_addr %0d\n\tframes_65_127_addr %0d\n\tframes_128_255_addr %0d\n\tframes_256_511_addr %0d\n\tframes_512_1023_addr %0d\n\tframes_1024_1518_addr %0d\n\tframes_over_1518_addr %0d\n\tframes_below_64_addr %0d\n\n",
                    m_sequencer.get_full_name(), it, rx_stats.crc_err, rx_stats.over_mtu_addr, rx_stats.below_min_addr, rx_stats.bcast_frames_addr, rx_stats.mcast_frames_addr, rx_stats.fragment_frames_addr, rx_stats.jabber_frames_addr, rx_stats.trans_octets_addr,
                    rx_stats.frames_64_addr, rx_stats.frames_65_127_addr, rx_stats.frames_128_255_addr, rx_stats.frames_256_511_addr, rx_stats.frames_512_1023_addr, rx_stats.frames_1024_1518_addr, rx_stats.frames_over_1518_addr, rx_stats.frames_below_64_addr),
                UVM_LOW);

           `uvm_info(this.get_full_name(),
                $sformatf("TX channel %s  [%0d]\n\tSTATS tfc  %0d soc %0d dfc %0d sfc %0d\n",            m_sequencer.get_full_name(), it, tx_stats.tfc, tx_stats.soc, tx_stats.dfc, tx_stats.sfc),
                UVM_LOW);

            fork
                rx_stats.reset();
                tx_stats.reset();
            join

            #(40ns);

            fork
                rx_stats.start(null);
                tx_stats.start(null);
            join

           `uvm_info(this.get_full_name(),
                $sformatf("RX channel %s [%0d]\n\tAFTER RESET STATS trfc %0d cfc %0d dfc %0d bodfc %0d oroc %0d\n", m_sequencer.get_full_name(), it, rx_stats.trfc, rx_stats.cfc, rx_stats.dfc, rx_stats.bodfc, rx_stats.oroc),
                UVM_LOW);
           `uvm_info(this.get_full_name(),
                $sformatf("RX channel %s rfc  [%0d]\n\tcrc_err %0d\n\tover_mtu_addr %0d\n\t below_min_addr %0d\n\tbcast_frames_addr %0d\n\tmcast_frames_addr %0d\n\tfragment_frames_addr %0d\n\tjabber_frames_addr %0d\n\ttrans_octets_addr %0d\n\tframes_64_addr %0d\n\tframes_65_127_addr %0d\n\tframes_128_255_addr %0d\n\tframes_256_511_addr %0d\n\tframes_512_1023_addr %0d\n\tframes_1024_1518_addr %0d\n\tframes_over_1518_addr %0d\n\tframes_below_64_addr %0d\n\n",
                          m_sequencer.get_full_name(), it, rx_stats.crc_err, rx_stats.over_mtu_addr, rx_stats.below_min_addr, rx_stats.bcast_frames_addr, rx_stats.mcast_frames_addr, rx_stats.fragment_frames_addr, rx_stats.jabber_frames_addr, rx_stats.trans_octets_addr,
                          rx_stats.frames_64_addr, rx_stats.frames_65_127_addr, rx_stats.frames_128_255_addr, rx_stats.frames_256_511_addr, rx_stats.frames_512_1023_addr, rx_stats.frames_1024_1518_addr, rx_stats.frames_over_1518_addr, rx_stats.frames_below_64_addr),
                UVM_LOW);
           `uvm_info(this.get_full_name(),
                $sformatf("TX channel %s [%0d]\n\tAFTER RESET STATS tfc  %0d soc %0d dfc %0d sfc %0d\n",            m_sequencer.get_full_name(), it, tx_stats.tfc, tx_stats.soc, tx_stats.dfc, tx_stats.sfc),
                UVM_LOW);

            if (rx_stats.trfc != 0 || rx_stats.cfc != 0 || rx_stats.dfc != 0 || rx_stats.bodfc != 0 ||  /*rx_stats.oroc != 0 ||*/
                tx_stats.tfc != 0  || tx_stats.soc != 0 || tx_stats.dfc != 0 || tx_stats.sfc != 0) begin
                `uvm_fatal(m_sequencer.get_full_name(), "Some statistic is not set to zero after reset!\n");
            end
        end


        //Send end to other sequences.
        usr_rx_meta.wait_for_sequence_state(UVM_FINISHED);
        usr_rx_data.wait_for_sequence_state(UVM_FINISHED);
        eth_rx_data.wait_for_sequence_state(UVM_FINISHED);
        eth_rx_meta.wait_for_sequence_state(UVM_FINISHED);

        seq_sync_end.send_stop();
        eth_rst.wait_for_sequence_state(UVM_FINISHED);
        usr_tx_data.wait_for_sequence_state(UVM_FINISHED);
        usr_tx_hdr.wait_for_sequence_state(UVM_FINISHED);
        eth_tx.wait_for_sequence_state(UVM_FINISHED);
    endtask

endclass

class virt_sequence_port_stop #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, int unsigned ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_network_mod_env::virt_sequence_port_stop #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_object_param_utils(uvm_network_mod_e_tile_env::virt_sequence_port_stop #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));
    `uvm_declare_p_sequencer(uvm_network_mod_e_tile_env::sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH))

    uvm_sequence #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)) eth_rx_data;
    uvm_sequence #(uvm_logic_vector::sequence_item #(6))                eth_rx_meta;
    uvm_sequence #(uvm_avst::sequence_item #(ETH_PORT_CHAN, 1, REGION_SIZE * BLOCK_SIZE, ITEM_WIDTH, 1)) eth_tx;

    protected uvm_common::sequences_cfg_sync#(2) seq_sync_eth_rx;

    protected uvm_logic_vector_array::config_sequence eth_rx_seq_cfg;

    function new(string name = "virt_sequence_port_stop");
        super.new(name);
        eth_rx_seq_cfg = null;
    endfunction

    function int unsigned rx_transaction_count();
        return super.rx_transaction_count() + seq_sync_eth_rx.data.transactions[0];
    endfunction

    function void packet_size_set(uvm_logic_vector_array::config_sequence usr_rx_seq_cfg, uvm_logic_vector_array::config_sequence eth_rx_seq_cfg);
        super.packet_size_set(usr_rx_seq_cfg);
        this.eth_rx_seq_cfg = eth_rx_seq_cfg;
    endfunction

    task pre_body();
        uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH)                           lib_eth_rx_data;
        //uvm_logic_vector::sequence_simple#(6)                                       lib_eth_rx_meta;
        uvm_avst::sequence_lib_tx#(ETH_PORT_CHAN, 1, REGION_SIZE * BLOCK_SIZE, ITEM_WIDTH,  1)  lib_eth_tx;

        super.pre_body();

        // ETH SEQURENCE RX
        seq_sync_eth_rx = uvm_common::sequences_cfg_sync#(2)::type_id::create("seq_sync_eth_rx", m_sequencer);
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_rx_data, "", "state", seq_sync_eth_rx.cfg[0]);
        lib_eth_rx_data = uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH)::type_id::create("eth_rx_data", p_sequencer.eth_rx_data);
        lib_eth_rx_data.max_random_count = 100;
        lib_eth_rx_data.min_random_count = 10;
        lib_eth_rx_data.init_sequence();

        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_rx_meta, "", "state", seq_sync_eth_rx.cfg[1]);
        //lib_eth_rx_meta = //uvm_logic_vector::sequence_simple#(6)::type_id::create("eth_rx_meta", p_sequencer.eth_rx_meta);
        eth_rx_meta = uvm_network_mod_env::sequence_logic_vector#(6)::type_id::create("eth_rx_meta", p_sequencer.eth_rx_meta);
        //lib_eth_rx_meta.config_set();

        // ETH SEQURENCE TX
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_tx, "", "state", seq_sync_end);
        lib_eth_tx = uvm_avst::sequence_lib_tx#(ETH_PORT_CHAN, 1, REGION_SIZE * BLOCK_SIZE, ITEM_WIDTH,  1)::type_id::create("eth_tx", p_sequencer.eth_tx);
        lib_eth_tx.init_sequence();
        lib_eth_tx.max_random_count = 100;
        lib_eth_tx.min_random_count = 10;

        eth_rx_data  = lib_eth_rx_data;
        //eth_rx_meta  = lib_eth_rx_meta;
        eth_tx       = lib_eth_tx;
    endtask

    task body();
        uvm_common::sequence_cfg state;

        seq_sync_end.clear();
        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot cast sequence synchronization");
        end

        fork
            while (!seq_sync_end.stopped()) begin
                assert(eth_rst.randomize());
                eth_rst.start(p_sequencer.eth_rst);
            end

            while (!seq_sync_end.stopped()) begin
                assert(usr_tx_data.randomize());
                usr_tx_data.start(p_sequencer.usr_tx_data);
            end
            while (!seq_sync_end.stopped()) begin
                assert(usr_tx_hdr.randomize());
                usr_tx_hdr.start(p_sequencer.usr_tx_hdr);
            end

            while (!seq_sync_end.stopped()) begin
                assert(eth_tx.randomize());
                eth_tx.start(p_sequencer.eth_tx);
            end
        join_none

        while(!state.stopped()) begin
            #(300ns);
        end

        //Send end to other sequences.
        seq_sync_end.send_stop();
        eth_rst.wait_for_sequence_state(UVM_FINISHED);
        usr_tx_data.wait_for_sequence_state(UVM_FINISHED);
        usr_tx_hdr.wait_for_sequence_state(UVM_FINISHED);
        eth_tx.wait_for_sequence_state(UVM_FINISHED);
    endtask

endclass

class virt_sequence_simple #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, int unsigned ETH_PORT_CHAN[ETH_PORTS], MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_network_mod_env::virt_sequence_simple #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_object_param_utils(uvm_network_mod_e_tile_env::virt_sequence_simple #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    protected uvm_logic_vector_array::config_sequence eth_rx_seq_cfg[ETH_PORTS];

    function new(string name = "virt_sequence_simple");
        super.new(name);
    endfunction

    task pre_body();
        super.pre_body();
        
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            virt_sequence_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH) cast_virt_sequence_port;
            assert($cast(cast_virt_sequence_port, port[it]))
            else begin
                `uvm_fatal(this.get_full_name(), "\n\tCast failed")
            end

            cast_virt_sequence_port.packet_size_set(usr_rx_seq_cfg[it], eth_rx_seq_cfg[it]);
        end
    endtask

    function void packet_size_set(int unsigned min = 64, int unsigned max = 1500);
        super.packet_size_set(min, max);

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            eth_rx_seq_cfg[it] = new($sformatf("eth_rx_seq_cfg_%0d", it));
            eth_rx_seq_cfg[it].array_size_set(min, max);
        end
    endfunction

    task body();
        logic [ETH_PORTS-1:0] port_end = '0;
        int unsigned transactions = 0;

        // RANDOMIZATION
        assert(usr_rst.randomize());
        assert(mi_rst.randomize());
        assert(mi_phy_rst.randomize());
        assert(mi_pmd_rst.randomize());
        assert(tsu_rst.randomize());

        fork
            usr_rst.start(p_sequencer.usr_rst);
            mi_rst.start(p_sequencer.mi_rst);
            mi_phy_rst.start(p_sequencer.mi_phy_rst);
            mi_pmd_rst.start(p_sequencer.mi_pmd_rst);
            tsu_rst.start(p_sequencer.tsu_rst);
        join_none

        for (int unsigned it = 0; it <  ETH_PORTS; it++) begin
            fork
                automatic int unsigned index = it;
                begin
                    virt_sequence_port_stop #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH) seq_end;

                    port_end[index] = 0;
                    while (!seq_sync_port_end.stopped()) begin
                        assert(port[index].randomize());
                        //RUN DATA
                        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.port[index], "", "state", seq_sync_port_end);
                        port[index].start(p_sequencer.port[index]);
                        transactions += port[index].rx_transaction_count();
                        #0;
                    end

                    port_end[index] = 1;
                    // run end sequence
                    uvm_config_db#(uvm_common::sequence_cfg_signal)::set(p_sequencer.port[index], "", "state", seq_sync_end);
                    seq_end = virt_sequence_port_stop #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create($sformatf("seq_end_%0d", it), p_sequencer.port[index]);
                    assert(seq_end.randomize());
                    seq_end.start(p_sequencer.port[index], this);
                end
            join_none
        end

        //SEND STOP
        wait (transactions >= ETH_PORTS*30_000);
        seq_sync_port_end.send_stop();
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            wait(port_end[it] == 1);
        end
        seq_sync_end.send_stop();
        usr_rst.wait_for_sequence_state(UVM_FINISHED);
        mi_rst.wait_for_sequence_state(UVM_FINISHED);
        mi_phy_rst.wait_for_sequence_state(UVM_FINISHED);
        mi_pmd_rst.wait_for_sequence_state(UVM_FINISHED);
        tsu_rst.wait_for_sequence_state(UVM_FINISHED);
    endtask

endclass

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// END SEQUENCES
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
class virt_sequence_stop #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, int unsigned ETH_PORT_CHAN[ETH_PORTS], MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_network_mod_env::virt_sequence_stop #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_object_param_utils(uvm_network_mod_e_tile_env::virt_sequence_stop #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    protected uvm_logic_vector_array::config_sequence eth_rx_seq_cfg[ETH_PORTS];
    
    function new(string name = "virt_sequence_stop");
        super.new(name);
    endfunction

    function void packet_size_set(int unsigned min = 64, int unsigned max = 1500);
        super.packet_size_set(min, max);

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            eth_rx_seq_cfg[it] = new($sformatf("eth_rx_seq_cfg_%0d", it));
            eth_rx_seq_cfg[it].array_size_set(min, max);
        end
    endfunction

    task body();
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
