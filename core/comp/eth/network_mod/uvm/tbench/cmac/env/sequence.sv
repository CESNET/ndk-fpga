// sequence.sv: Virtual sequences
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>
//            Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class virt_sequence_port #(
    int unsigned ETH_TX_HDR_WIDTH,
    int unsigned ETH_RX_HDR_WIDTH,

    int unsigned ITEM_WIDTH,
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,

    int unsigned ETH_PORT_CHAN,

    int unsigned MI_DATA_WIDTH,
    int unsigned MI_ADDR_WIDTH
) extends uvm_network_mod_env::virt_sequence_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_object_param_utils(uvm_network_mod_cmac_env::virt_sequence_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH))
    `uvm_declare_p_sequencer(uvm_network_mod_cmac_env::sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH))

    bit initialized = 0;

    uvm_sequence #(uvm_logic_vector_array::sequence_item #(8)) eth_tx_packet;
    uvm_sequence #(uvm_logic_vector::sequence_item       #(1)) eth_tx_error;
    uvm_sequence #(uvm_lbus::sequence_item)                    eth_rx;

    protected uvm_common::sequences_cfg_sync #(2) seq_sync_eth_tx;

    protected uvm_logic_vector_array::config_sequence eth_tx_seq_cfg;

    // Constructor
    function new(string name = "virt_sequence_port");
        super.new(name);
    endfunction

    function int unsigned rx_transaction_count();
        return super.rx_transaction_count() + seq_sync_eth_tx.data.transactions[0];
    endfunction

    function void packet_size_set(uvm_logic_vector_array::config_sequence usr_rx_seq_cfg, uvm_logic_vector_array::config_sequence eth_tx_seq_cfg);
        super.packet_size_set(usr_rx_seq_cfg);
        this.eth_tx_seq_cfg = eth_tx_seq_cfg;
    endfunction

    task pre_body();
        uvm_packet_generators::sequence_flowtest #(8) lib_eth_tx_packet;
        uvm_lbus::sequence_library_rx                 seq_eth_rx;

        super.pre_body();

        // TX eth packet sequence
        seq_sync_eth_tx = uvm_common::sequences_cfg_sync#(2)::type_id::create("seq_sync_eth_tx", m_sequencer);
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_tx_packet, "", "state", seq_sync_eth_tx.cfg[0]);
        lib_eth_tx_packet = uvm_packet_generators::sequence_flowtest #(8)::type_id::create("lib_eth_tx_packet", p_sequencer.eth_tx_packet);
        lib_eth_tx_packet.generated_config = 1;
        lib_eth_tx_packet.generated_profile = 1;
        lib_eth_tx_packet.config_filepath = { "./", p_sequencer.get_full_name(), ".", "config.yaml" };
        lib_eth_tx_packet.profile_filepath  = { "./", p_sequencer.get_full_name(), ".", "profile.csv" };

        if (initialized == 0) begin
            assert(m_sequence_mac_check_configuration.randomize());
        end
        // Add MAC Check addresses to the configuration of the flowtest sequence
        lib_eth_tx_packet.cfg.mac_addresses = m_sequence_mac_check_configuration.addresses;

        // TX eth error sequence
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_tx_error, "", "state", seq_sync_eth_tx.cfg[1]);
        eth_tx_error = uvm_network_mod_env::sequence_logic_vector#(1)::type_id::create("eth_tx_error", p_sequencer.eth_tx_error);

        // RX eth sequence
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_rx, "", "state", seq_sync_end);
        seq_eth_rx = uvm_lbus::sequence_library_rx::type_id::create("eth_rx", p_sequencer.eth_rx);
        seq_eth_rx.init_sequence();

        eth_tx_packet = lib_eth_tx_packet;
        eth_rx        = seq_eth_rx;
    endtask

    task body();
        uvm_status_e   status;
        uvm_reg_data_t data;
        uvm_common::sequence_cfg state;

        assert(uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state));
        assert(state != null);

        seq_sync_end.clear();

        fork
            do begin
                assert(eth_rst.randomize());
                eth_rst.start(p_sequencer.eth_rst);
            end while (!seq_sync_end.stopped());
        join_none

        #(400ns);

        if (initialized == 0) begin
            for (int unsigned it = 0; it < ETH_PORT_CHAN; it++) begin
                m_sequence_mac_check_configuration.start(p_sequencer);

                fork
                    p_sequencer.regmodel.channel[it].rx_mac.enable.write(status, 1'h1);
                    p_sequencer.regmodel.channel[it].tx_mac.enable.write(status, 1'h1);
                join;

                fork
                    p_sequencer.regmodel.channel[it].rx_mac.enable.read(status, data);
                    p_sequencer.regmodel.channel[it].tx_mac.enable.read(status, data);
                join;
            end

            initialized = 1;
        end

        fork
            do begin
                assert(usr_rx_data.randomize());
                usr_rx_data.start(p_sequencer.usr_rx_data);
            end while (!seq_sync_usr_rx.cfg[0].stopped());
            do begin
                assert(usr_rx_meta.randomize());
                usr_rx_meta.start(p_sequencer.usr_rx_meta);
            end while (!seq_sync_usr_rx.cfg[1].stopped());

            do begin
                assert(usr_tx_data.randomize());
                usr_tx_data.start(p_sequencer.usr_tx_data);
            end while (!seq_sync_end.stopped());
            do begin
                assert(usr_tx_hdr.randomize());
                usr_tx_hdr.start(p_sequencer.usr_tx_hdr);
            end while (!seq_sync_end.stopped());

            do begin
                assert(eth_tx_packet.randomize());
                eth_tx_packet.start(p_sequencer.eth_tx_packet);
            end while (!seq_sync_eth_tx.cfg[0].stopped());
            do begin
                assert(eth_tx_error.randomize());
                eth_tx_error.start(p_sequencer.eth_tx_error);
            end while (!seq_sync_eth_tx.cfg[1].stopped());

            do begin
                assert(eth_rx.randomize());
                eth_rx.start(p_sequencer.eth_rx);
            end while (!seq_sync_end.stopped());
        join_none

        while ((state == null || !state.stopped()) &&
               (this.rx_transaction_count() < transactions_approx)
           ) begin
            #(300ns);
        end
        // Stop data sequences
        seq_sync_usr_rx.send_stop();
        seq_sync_eth_tx.send_stop();

        // Read statistics
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

            `uvm_info(m_sequencer.get_full_name(), $sformatf("RX channel[%0d] STATS\n\t%s\n", it, rx_stats.convert2string()), UVM_LOW);
            `uvm_info(m_sequencer.get_full_name(), $sformatf("TX channel[%0d] STATS\n\t%s\n", it, tx_stats.convert2string()), UVM_LOW);

            fork
                rx_stats.reset();
                tx_stats.reset();
            join

            fork
                rx_stats.start(null);
                tx_stats.start(null);
            join

            `uvm_info(m_sequencer.get_full_name(), $sformatf("RX channel[%0d] STATS AFTER RESET\n\t%s\n", it, rx_stats.convert2string()), UVM_LOW);
            `uvm_info(m_sequencer.get_full_name(), $sformatf("TX channel[%0d] STATS AFTER RESET\n\t%s\n", it, tx_stats.convert2string()), UVM_LOW);

            if (!rx_stats.zero() || !tx_stats.zero()) begin
                `uvm_fatal(m_sequencer.get_full_name(), "Some statistic is not set to zero after reset!\n");
            end
        end

        // Wait for the end of the data sequences
        usr_rx_meta.wait_for_sequence_state(UVM_FINISHED);
        usr_rx_data.wait_for_sequence_state(UVM_FINISHED);
        eth_tx_packet.wait_for_sequence_state(UVM_FINISHED);
        eth_tx_error.wait_for_sequence_state(UVM_FINISHED);

        // Stop other sequences
        seq_sync_end.send_stop();
        // Wait for the end of the other sequences
        eth_rst.wait_for_sequence_state(UVM_FINISHED);
        usr_tx_data.wait_for_sequence_state(UVM_FINISHED);
        usr_tx_hdr.wait_for_sequence_state(UVM_FINISHED);
        eth_rx.wait_for_sequence_state(UVM_FINISHED);
    endtask

endclass

class virt_sequence_port_stop #(
    int unsigned ETH_TX_HDR_WIDTH,
    int unsigned ETH_RX_HDR_WIDTH,

    int unsigned ITEM_WIDTH,
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,

    int unsigned ETH_PORT_CHAN,

    int unsigned MI_DATA_WIDTH,
    int unsigned MI_ADDR_WIDTH
) extends uvm_network_mod_env::virt_sequence_port_stop #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_object_param_utils(uvm_network_mod_cmac_env::virt_sequence_port_stop #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH));
    `uvm_declare_p_sequencer(uvm_network_mod_cmac_env::sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH))

    uvm_sequence #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)) eth_tx_packet;
    uvm_sequence #(uvm_logic_vector::sequence_item       #(6))          eth_tx_error;
    uvm_sequence #(uvm_lbus::sequence_item)                             eth_rx;

    protected uvm_common::sequences_cfg_sync#(2) seq_sync_eth_tx;

    protected uvm_logic_vector_array::config_sequence eth_tx_seq_cfg;

    // Constructor
    function new(string name = "virt_sequence_port_stop");
        super.new(name);
    endfunction

    function int unsigned rx_transaction_count();
        return super.rx_transaction_count() + seq_sync_eth_tx.data.transactions[0];
    endfunction

    function void packet_size_set(uvm_logic_vector_array::config_sequence usr_rx_seq_cfg, uvm_logic_vector_array::config_sequence eth_tx_seq_cfg);
        super.packet_size_set(usr_rx_seq_cfg);
        this.eth_tx_seq_cfg = eth_tx_seq_cfg;
    endfunction

    task pre_body();
        uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH) lib_eth_tx_packet;
        uvm_lbus::sequence_library_rx                     seq_eth_rx;

        super.pre_body();

        // TX eth packet sequence
        seq_sync_eth_tx = uvm_common::sequences_cfg_sync#(2)::type_id::create("seq_sync_eth_tx", m_sequencer);
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_tx_packet, "", "state", seq_sync_eth_tx.cfg[0]);
        lib_eth_tx_packet = uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH)::type_id::create("eth_tx_packet", p_sequencer.eth_tx_packet);
        lib_eth_tx_packet.max_random_count = 20;
        lib_eth_tx_packet.min_random_count = 10;
        lib_eth_tx_packet.init_sequence();

        // TX eth error sequence
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_tx_error, "", "state", seq_sync_eth_tx.cfg[1]);
        eth_tx_error = uvm_network_mod_env::sequence_logic_vector#(6)::type_id::create("eth_tx_error", p_sequencer.eth_tx_error);

        // RX eth sequence
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_rx, "", "state", seq_sync_end);
        seq_eth_rx = uvm_lbus::sequence_library_rx::type_id::create("eth_rx", p_sequencer.eth_rx);
        seq_eth_rx.init_sequence();

        eth_tx_packet = lib_eth_tx_packet;
        eth_rx        = seq_eth_rx;
    endtask

    task body();
        uvm_common::sequence_cfg state;

        seq_sync_end.clear();

        assert(uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state))
        else begin
            `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot get a sequence port state object");
        end

        fork
            do begin
                assert(eth_rst.randomize());
                eth_rst.start(p_sequencer.eth_rst);
            end while (!seq_sync_end.stopped());

            do begin
                assert(usr_tx_data.randomize());
                usr_tx_data.start(p_sequencer.usr_tx_data);
            end while (!seq_sync_end.stopped());
            do begin
                assert(usr_tx_hdr.randomize());
                usr_tx_hdr.start(p_sequencer.usr_tx_hdr);
            end while (!seq_sync_end.stopped());

            do begin
                assert(eth_rx.randomize());
                eth_rx.start(p_sequencer.eth_rx);
            end while (!seq_sync_end.stopped());
        join_none

        while(!state.stopped()) begin
            #(300ns);
        end

        // Stop the sequences
        seq_sync_end.send_stop();
        // Wait for the end of the sequences
        eth_rst.wait_for_sequence_state(UVM_FINISHED);
        usr_tx_data.wait_for_sequence_state(UVM_FINISHED);
        usr_tx_hdr.wait_for_sequence_state(UVM_FINISHED);
        eth_rx.wait_for_sequence_state(UVM_FINISHED);
    endtask

endclass

class virt_sequence_simple #(
    int unsigned ETH_PORTS,
    int unsigned ETH_TX_HDR_WIDTH,
    int unsigned ETH_RX_HDR_WIDTH,

    int unsigned ITEM_WIDTH,
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,

    int unsigned ETH_PORT_CHAN[ETH_PORTS],

    int unsigned MI_DATA_WIDTH,
    int unsigned MI_ADDR_WIDTH
) extends uvm_network_mod_env::virt_sequence_simple #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_object_param_utils(uvm_network_mod_cmac_env::virt_sequence_simple #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    protected uvm_logic_vector_array::config_sequence eth_tx_seq_cfg[ETH_PORTS];

    // Constructor
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

            cast_virt_sequence_port.packet_size_set(usr_rx_seq_cfg[it], eth_tx_seq_cfg[it]);
        end
    endtask

    function void packet_size_set(int unsigned min = 64, int unsigned max = 1500);
        super.packet_size_set(min, max);

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            eth_tx_seq_cfg[it] = new();
            eth_tx_seq_cfg[it].array_size_set(min, max);
        end
    endfunction

    task body();
        logic [ETH_PORTS-1:0] port_end = '0;
        int unsigned transactions = 0;

        // Randomization
        assert(usr_rst.randomize());
        assert(mi_rst.randomize());
        assert(mi_phy_rst.randomize());
        assert(mi_pmd_rst.randomize());
        assert(tsu_rst.randomize());

        // Start of the reset sequences
        fork
            usr_rst.start(p_sequencer.usr_rst);
            mi_rst.start(p_sequencer.mi_rst);
            mi_phy_rst.start(p_sequencer.mi_phy_rst);
            mi_pmd_rst.start(p_sequencer.mi_pmd_rst);
            tsu_rst.start(p_sequencer.tsu_rst);
        join_none

        fork
            forever begin
                assert(tsu.randomize());
                tsu.start(p_sequencer.tsu);
            end
        join_none

        // Run sequences
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            fork
                int unsigned index = it;
                begin
                    virt_sequence_port_stop #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH) seq_end;

                    port_end[index] = 0;

                    while (!seq_sync_port_end.stopped()) begin
                        assert(port[index].randomize());
                        // Run a data sequence
                        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.port[index], "", "state", seq_sync_port_end);
                        port[index].start(p_sequencer.port[index]);
                        transactions += port[index].rx_transaction_count();
                        #0;
                    end

                    port_end[index] = 1;
                    // Run an end sequence
                    uvm_config_db#(uvm_common::sequence_cfg_signal)::set(p_sequencer.port[index], "", "state", seq_sync_end);
                    seq_end = virt_sequence_port_stop #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create($sformatf("seq_end_%0d", it), p_sequencer.port[index]);
                    assert(seq_end.randomize());
                    seq_end.start(p_sequencer.port[index], this);
                end
            join_none
        end

        // Stop the sequences
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
class virt_sequence_stop #(
    int unsigned ETH_PORTS,
    int unsigned ETH_TX_HDR_WIDTH,
    int unsigned ETH_RX_HDR_WIDTH,

    int unsigned ITEM_WIDTH,
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,

    int unsigned ETH_PORT_CHAN[ETH_PORTS],

    int unsigned MI_DATA_WIDTH,
    int unsigned MI_ADDR_WIDTH
) extends uvm_network_mod_env::virt_sequence_stop #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_object_param_utils(uvm_network_mod_cmac_env::virt_sequence_stop #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    protected uvm_logic_vector_array::config_sequence eth_tx_seq_cfg[ETH_PORTS];

    // Constructor
    function new(string name = "virt_sequence_stop");
        super.new(name);
    endfunction

    function void packet_size_set(int unsigned min = 64, int unsigned max = 1500);
        super.packet_size_set(min, max);

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            eth_tx_seq_cfg[it] = new();
            eth_tx_seq_cfg[it].array_size_set(min, max);
        end
    endfunction

    task body();
        // Randomization
        assert(usr_rst.randomize());
        assert(mi_rst.randomize());
        assert(mi_phy_rst.randomize());
        assert(mi_pmd_rst.randomize());
        assert(tsu_rst.randomize());

        // Start of the reset sequences
        fork
            do begin
                usr_rst.start(p_sequencer.usr_rst, this);
            end while (!seq_sync_end.stopped());
            do begin
                mi_rst.start(p_sequencer.mi_rst, this);
            end while (!seq_sync_end.stopped());
            do begin
                mi_phy_rst.start(p_sequencer.mi_phy_rst, this);
            end while (!seq_sync_end.stopped());
            do begin
                mi_pmd_rst.start(p_sequencer.mi_pmd_rst, this);
            end while (!seq_sync_end.stopped());
            do begin
                tsu_rst.start(p_sequencer.tsu_rst, this);
            end while (!seq_sync_end.stopped());
        join_none

        fork
            forever begin
                assert(tsu.randomize());
                tsu.start(p_sequencer.tsu);
            end
        join_none

        // Run the sequences
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
        // Stop the sequences
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
