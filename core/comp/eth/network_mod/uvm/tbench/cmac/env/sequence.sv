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
) extends
    uvm_network_mod_env::virt_sequence_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE,
                                              BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_object_param_utils(
        uvm_network_mod_cmac_env::virt_sequence_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS,
            REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH))
    `uvm_declare_p_sequencer(
        uvm_network_mod_cmac_env::sequencer_port #(
            ETH_TX_HDR_WIDTH,
            ETH_RX_HDR_WIDTH,
            ITEM_WIDTH,
            REGIONS,
            REGION_SIZE,
            BLOCK_SIZE,
            ETH_PORT_CHAN[0],
            MI_DATA_WIDTH,
            MI_ADDR_WIDTH
        ))

    bit initialized = 0;

    uvm_sequence #(uvm_logic_vector_array::sequence_item #(8)) eth_rx_packet;
    uvm_sequence #(uvm_logic_vector::sequence_item       #(1)) eth_rx_error;

    protected uvm_common::sequences_cfg_sync #(2) seq_sync_eth_tx;

    protected uvm_logic_vector_array::config_sequence eth_tx_seq_cfg;

    // Constructor
    function new(string name = "virt_sequence_port");
        super.new(name);
    endfunction

    function int unsigned rx_transaction_count();
        return super.rx_transaction_count() + seq_sync_eth_tx.data.transactions[0];
    endfunction

    function void packet_size_set(uvm_logic_vector_array::config_sequence usr_rx_seq_cfg,
                                  uvm_logic_vector_array::config_sequence eth_tx_seq_cfg);
        super.packet_size_set(usr_rx_seq_cfg);
        this.eth_tx_seq_cfg = eth_tx_seq_cfg;
    endfunction

    task pre_body();
        uvm_packet_generators::sequence_flowtest #(8) lib_eth_tx_packet;

        super.pre_body();

        // TX eth packet sequence
        seq_sync_eth_tx = uvm_common::sequences_cfg_sync#(2)::type_id::create("seq_sync_eth_tx", m_sequencer);
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_rx_packet, "", "state", seq_sync_eth_tx.cfg[0]);
        // verilog_lint: waive line-length
        lib_eth_tx_packet = uvm_packet_generators::sequence_flowtest #(8)::type_id::create("lib_eth_tx_packet", p_sequencer.eth_rx_packet);
        lib_eth_tx_packet.generated_config = 1;
        lib_eth_tx_packet.generated_profile = 1;
        lib_eth_tx_packet.config_filepath = { "./", p_sequencer.get_full_name(), ".", "config.yaml" };
        lib_eth_tx_packet.profile_filepath  = { "./", p_sequencer.get_full_name(), ".", "profile.csv" };

        // TX eth error sequence
        uvm_config_db#(uvm_common::sequence_cfg)::set(p_sequencer.eth_rx_error, "", "state", seq_sync_eth_tx.cfg[1]);
        // verilog_lint: waive line-length
        eth_rx_error = uvm_network_mod_env::sequence_logic_vector#(1)::type_id::create("eth_rx_error", p_sequencer.eth_rx_error);

        // RX eth sequence
        eth_rx_packet = lib_eth_tx_packet;
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
                assert(m_sequence_mac_check_configuration.randomize());
                m_sequence_mac_check_configuration.start(p_sequencer);

                assert(m_sequence_frame_length_configuration.randomize());
                m_sequence_frame_length_configuration.start(p_sequencer);

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

        // Add MAC Check addresses to the configuration of the flowtest sequence
        begin
            uvm_packet_generators::sequence_flowtest #(8) dummy;
            assert($cast(dummy, eth_rx_packet));
            add_mac_check_addresses(dummy.cfg);
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
                assert(eth_rx_packet.randomize());
                eth_rx_packet.start(p_sequencer.eth_rx_packet);
            end while (!seq_sync_eth_tx.cfg[0].stopped());
            do begin
                assert(eth_rx_error.randomize());
                eth_rx_error.start(p_sequencer.eth_rx_error);
            end while (!seq_sync_eth_tx.cfg[1].stopped());
        join_none

        while ((state == null || !state.stopped()) &&
               (this.rx_transaction_count() < transactions_approx)
           ) begin
            #(300ns);
        end
        // Stop data sequences
        seq_sync_usr_rx.send_stop();
        seq_sync_eth_tx.send_stop();

        #(1us);

        // Read statistics
        for (int unsigned it = 0; it < ETH_PORT_CHAN; it++) begin
            uvm_network_mod_env::read_rx_counters#(RX_MAC_COUNT) rx_stats;
            uvm_network_mod_env::read_tx_counters                tx_stats;

            rx_stats = uvm_network_mod_env::read_rx_counters#(RX_MAC_COUNT)::type_id::create("rx_stats", m_sequencer);
            rx_stats.set_regmodel(p_sequencer.regmodel.channel[it].rx_mac);
            tx_stats = uvm_network_mod_env::read_tx_counters::type_id::create("tx_stats", m_sequencer);
            tx_stats.set_regmodel(p_sequencer.regmodel.channel[it].tx_mac);

            fork
                begin
                    rx_stats.start(null);
                    `uvm_info(m_sequencer.get_full_name(), $sformatf(
                              "RX channel[%0d] STATS\n\t%s\n", it, rx_stats.convert2string()), UVM_LOW);
                    rx_stats.reset();
                    rx_stats.start(null);
                end

                begin
                    tx_stats.start(null);
                    `uvm_info(m_sequencer.get_full_name(), $sformatf(
                              "TX channel[%0d] STATS\n\t%s\n", it, tx_stats.convert2string()), UVM_LOW);
                    tx_stats.reset();
                    tx_stats.start(null);
                end
            join

            `uvm_info(m_sequencer.get_full_name(), $sformatf(
                      "RX channel[%0d] STATS AFTER RESET\n\t%s\n", it, rx_stats.convert2string()), UVM_LOW);
            `uvm_info(m_sequencer.get_full_name(), $sformatf(
                      "TX channel[%0d] STATS AFTER RESET\n\t%s\n", it, tx_stats.convert2string()), UVM_LOW);

            if (!rx_stats.zero() || !tx_stats.zero()) begin
                `uvm_fatal(m_sequencer.get_full_name(), "Some statistic is not set to zero after reset!\n");
            end
        end

        // Wait for the end of the data sequences
        usr_rx_meta.wait_for_sequence_state(UVM_FINISHED);
        usr_rx_data.wait_for_sequence_state(UVM_FINISHED);
        eth_rx_packet.wait_for_sequence_state(UVM_FINISHED);
        eth_rx_error.wait_for_sequence_state(UVM_FINISHED);

        // Stop other sequences
        seq_sync_end.send_stop();
        // Wait for the end of the other sequences
        eth_rst.wait_for_sequence_state(UVM_FINISHED);
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
) extends
    uvm_network_mod_env::virt_sequence_simple #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS,
                                                REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_object_param_utils(
        uvm_network_mod_cmac_env::virt_sequence_simple #(
            ETH_PORTS,
            ETH_TX_HDR_WIDTH,
            ETH_RX_HDR_WIDTH,
            ITEM_WIDTH,
            REGIONS,
            REGION_SIZE,
            BLOCK_SIZE,
            ETH_PORT_CHAN,
            MI_DATA_WIDTH,
            MI_ADDR_WIDTH
        ))

    protected uvm_logic_vector_array::config_sequence eth_tx_seq_cfg[ETH_PORTS];

    // Constructor
    function new(string name = "virt_sequence_simple");
        super.new(name);
    endfunction

    task pre_body();
        super.pre_body();

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            virt_sequence_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE,
                                 ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH) cast_virt_sequence_port;
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

        // Start of the reset sequences
        fork
            usr_rst.start(p_sequencer.usr_rst);
            mi_rst.start(p_sequencer.mi_rst);
            mi_phy_rst.start(p_sequencer.mi_phy_rst);
            mi_pmd_rst.start(p_sequencer.mi_pmd_rst);
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

                    port_end[index] = 0;
                    while (!seq_sync_port_end.stopped()) begin
                        assert(port[index].randomize());
                        // Run a data sequence
                        uvm_config_db #(uvm_common::sequence_cfg)::set(p_sequencer.port[index], "", "state",
                                                                      seq_sync_port_end);
                        port[index].start(p_sequencer.port[index]);
                        transactions += port[index].rx_transaction_count();
                        #0;
                    end
                    port_end[index] = 1;
                end
            join_none
        end

        // Stop the sequences
        wait (transactions >= ETH_PORTS*20_000);
        seq_sync_port_end.send_stop();
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            wait(port_end[it] == 1);
        end
        seq_sync_end.send_stop();
        usr_rst.wait_for_sequence_state(UVM_FINISHED);
        mi_rst.wait_for_sequence_state(UVM_FINISHED);
        mi_phy_rst.wait_for_sequence_state(UVM_FINISHED);
        mi_pmd_rst.wait_for_sequence_state(UVM_FINISHED);
    endtask
endclass


