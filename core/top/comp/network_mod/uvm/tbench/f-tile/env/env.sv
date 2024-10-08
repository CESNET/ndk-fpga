// env.sv: Environment for Intel F-Tile device
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env #(
    string ETH_CORE_ARCH,
    int unsigned ETH_PORTS,

    int unsigned ETH_PORT_SPEED[ETH_PORTS-1:0],
    int unsigned ETH_PORT_CHAN[ETH_PORTS-1 : 0],

    int unsigned ETH_TX_HDR_WIDTH,
    int unsigned ETH_RX_HDR_WIDTH,

    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,

    int unsigned MI_DATA_WIDTH,
    int unsigned MI_ADDR_WIDTH
) extends uvm_network_mod_env::env #(
        ETH_CORE_ARCH,
        ETH_PORTS,
        ETH_PORT_SPEED,
        ETH_PORT_CHAN,
        ETH_TX_HDR_WIDTH,
        ETH_RX_HDR_WIDTH,
        REGIONS,
        REGION_SIZE,
        BLOCK_SIZE,
        ITEM_WIDTH,
        MI_DATA_WIDTH,
        MI_ADDR_WIDTH
    );
    `uvm_component_param_utils(uvm_network_mod_f_tile_env::env #(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    // Intel Mac Seg environments
    protected uvm_logic_vector_array_intel_mac_seg::env_rx #(SEGMENTS) m_eth_rx[ETH_PORTS];
    protected uvm_logic_vector_array_intel_mac_seg::env_tx #(SEGMENTS) m_eth_tx[ETH_PORTS];

    tx_error_trimmer m_tx_error_trimmer[ETH_PORTS];

    // Constructor
    function new(string name = "env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        // -------------------------------------- //
        // Overriding the base components/objects //
        // -------------------------------------- //

        uvm_network_mod_env::sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::set_inst_override(
            uvm_network_mod_f_tile_env::sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH)::get_type(),
            "m_sequencer.*",
            this
        );

        uvm_network_mod_env::model #(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, REGIONS, ITEM_WIDTH, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH)::type_id::set_inst_override(
            uvm_network_mod_f_tile_env::model #(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, REGIONS, ITEM_WIDTH, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH)::get_type(),
            "m_scoreboard.m_model",
            this
        );

        uvm_network_mod_env::virt_sequence_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::set_type_override(
            uvm_network_mod_f_tile_env::virt_sequence_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH)::get_type()
        );
        uvm_network_mod_env::virt_sequence_port_stop #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::set_type_override(
            uvm_network_mod_f_tile_env::virt_sequence_port_stop #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH)::get_type()
        );
        uvm_network_mod_env::virt_sequence_simple #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::set_type_override(
            uvm_network_mod_f_tile_env::virt_sequence_simple #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH)::get_type()
        );
        uvm_network_mod_env::virt_sequence_stop #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::set_type_override(
            uvm_network_mod_f_tile_env::virt_sequence_stop #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH)::get_type()
        );

        // Build of base environment
        super.build_phase(phase);

        // --------------------------- //
        // Build of F-Tile environment //
        // --------------------------- //

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            uvm_logic_vector_array_intel_mac_seg::config_item cfg_eth_rx;
            uvm_logic_vector_array_intel_mac_seg::config_item cfg_eth_tx;

            cfg_eth_rx = new();
            cfg_eth_rx.active = UVM_ACTIVE;
            cfg_eth_rx.interface_name = $sformatf("vif_eth_rx_%0d", it);
            uvm_config_db #(uvm_logic_vector_array_intel_mac_seg::config_item)::set(this, $sformatf("m_eth_rx_%0d", it), "m_config", cfg_eth_rx);
            m_eth_rx[it] = uvm_logic_vector_array_intel_mac_seg::env_rx #(SEGMENTS)::type_id::create($sformatf("m_eth_rx_%0d", it), this);

            cfg_eth_tx = new();
            cfg_eth_tx.active = UVM_ACTIVE;
            cfg_eth_tx.interface_name = $sformatf("vif_eth_tx_%0d", it);
            uvm_config_db #(uvm_logic_vector_array_intel_mac_seg::config_item)::set(this, $sformatf("m_eth_tx_%0d", it), "m_config", cfg_eth_tx);
            m_eth_tx[it] = uvm_logic_vector_array_intel_mac_seg::env_tx #(SEGMENTS)::type_id::create($sformatf("m_eth_tx_%0d", it), this);
            
            m_tx_error_trimmer[it] = tx_error_trimmer::type_id::create($sformatf("m_tx_error_trimmer_%0d", it), this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // Connection of resets
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            m_eth_rst[it].sync_connect(m_eth_rx[it].reset_sync);
            m_eth_rst[it].sync_connect(m_eth_tx[it].reset_sync);
        end

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            m_eth_rx[it].analysis_port_packet.connect(m_scoreboard.eth_rx_data[it]);
            m_eth_rx[it].analysis_port_error.connect(m_scoreboard.eth_rx_hdr[it]);

            m_eth_tx[it].analysis_port_packet.connect(m_scoreboard.eth_tx_data[it]);

            m_eth_tx[it].analysis_port_error.connect(m_tx_error_trimmer[it].analysis_export);
            m_tx_error_trimmer[it].analysis_port.connect(m_scoreboard.eth_tx_hdr[it]);
        end

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH) cast_sequencer_port;
            assert($cast(cast_sequencer_port, m_sequencer.port[it]))
            else begin
                `uvm_fatal(this.get_full_name(), $sformatf("\n\tCast failed: %s", m_sequencer.port[it].get_full_name()))
            end

            cast_sequencer_port.eth_rx_data = m_eth_rx[it].m_sequencer.m_packet;
            cast_sequencer_port.eth_rx_meta = m_eth_rx[it].m_sequencer.m_error;
            cast_sequencer_port.eth_tx      = m_eth_tx[it].m_sequencer;
        end
    endfunction

endclass
