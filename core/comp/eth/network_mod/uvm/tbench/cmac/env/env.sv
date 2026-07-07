// env.sv: Environment for the Xilinx CMAC device
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
    `uvm_component_param_utils(
        uvm_network_mod_cmac_env::env #(
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
        ))

    // BYTE ARRAY LBUS environments
    protected uvm_logic_vector_array_lbus::env_rx m_eth_rx[ETH_PORTS];
    protected uvm_logic_vector_array_lbus::env_tx m_eth_tx[ETH_PORTS];

    tx_error_expander m_rx_error_expander[ETH_PORTS];

    // Constructor
    function new(string name = "env", uvm_component parent = null);
        super.new(name, parent);
    endfunction


    virtual function void eth_full_speed_set();
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            uvm_logic_vector_array_lbus::sequence_library_rx::type_id::set_inst_override(
                uvm_logic_vector_array_lbus::sequence_library_rx_speed::get_type(),
                $sformatf("m_eth_rx_%0d.*", it),
                this
            );

            uvm_lbus::sequence_library_tx::type_id::set_inst_override(
                uvm_lbus::sequence_library_tx_speed::get_type(),
                $sformatf("m_eth_tx_%0d.*", it),
                this
            );
        end
    endfunction

    function void build_phase(uvm_phase phase);
        // -------------------------------------- //
        // Overriding the base components/objects //
        // -------------------------------------- //

        uvm_network_mod_env::sequencer_port
            #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0],
              MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::set_inst_override(
            uvm_network_mod_cmac_env::sequencer_port
                #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0],
                  MI_DATA_WIDTH, MI_ADDR_WIDTH)::get_type(),
            "m_sequencer.*",
            this
        );

        uvm_network_mod_env::virt_sequence_port
            #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0],
              MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::set_type_override(
            uvm_network_mod_cmac_env::virt_sequence_port
                #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN[0],
                  MI_DATA_WIDTH, MI_ADDR_WIDTH)::get_type()
        );
        uvm_network_mod_env::virt_sequence_simple
            #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE,
              ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::set_type_override(
            uvm_network_mod_cmac_env::virt_sequence_simple
                #(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE,
                  ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH)::get_type()
        );

        // Build of base environment
        super.build_phase(phase);

        // ------------------------- //
        // Build of CMAC environment //
        // ------------------------- //

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            uvm_logic_vector_array_lbus::config_item cfg_eth_rx;
            uvm_logic_vector_array_lbus::config_item cfg_eth_tx;

            cfg_eth_rx = new();
            cfg_eth_rx.active = UVM_ACTIVE;
            cfg_eth_rx.interface_name = $sformatf("vif_eth_rx_%0d", it);
            uvm_config_db #(uvm_logic_vector_array_lbus::config_item)::set(this, $sformatf("m_eth_rx_%0d", it),
                                                                          "m_config", cfg_eth_rx);
            m_eth_rx[it] = uvm_logic_vector_array_lbus::env_rx::type_id::create($sformatf("m_eth_rx_%0d", it), this);

            cfg_eth_tx = new();
            cfg_eth_tx.active = UVM_ACTIVE;
            cfg_eth_tx.interface_name = $sformatf("vif_eth_tx_%0d", it);
            uvm_config_db #(uvm_logic_vector_array_lbus::config_item)::set(this, $sformatf("m_eth_tx_%0d", it),
                                                                          "m_config", cfg_eth_tx);
            m_eth_tx[it] = uvm_logic_vector_array_lbus::env_tx::type_id::create($sformatf("m_eth_tx_%0d", it), this);

            // verilog_lint: waive line-length
            m_rx_error_expander[it] = tx_error_expander::type_id::create($sformatf("m_rx_error_expander_%0d", it), this);
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
            // TX packet
            m_eth_rx[it].analysis_port_packet.connect(m_scoreboard.eth_rx_data[it]);
            // TX error
            m_eth_rx[it].analysis_port_error.connect(m_rx_error_expander[it].analysis_export);
            m_rx_error_expander[it].analysis_port.connect(m_scoreboard.eth_rx_hdr[it]);

            // RX packet
            m_eth_tx[it].analysis_port_packet.connect(m_scoreboard.eth_tx_data[it]);
            // RX error
            m_eth_tx[it].analysis_port_error.connect(m_scoreboard.eth_tx_hdr[it]);
        end

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE,
                             ETH_PORT_CHAN[0], MI_DATA_WIDTH, MI_ADDR_WIDTH) cast_sequencer_port;
            assert($cast(cast_sequencer_port, m_sequencer.port[it]))
            else begin
                `uvm_fatal(this.get_full_name(), $sformatf("\n\tCast failed: %s", m_sequencer.port[it].get_full_name()))
            end

            cast_sequencer_port.eth_rx_packet = m_eth_rx[it].m_sequencer.packet;
            cast_sequencer_port.eth_rx_error  = m_eth_rx[it].m_sequencer.error;
        end
    endfunction

endclass
