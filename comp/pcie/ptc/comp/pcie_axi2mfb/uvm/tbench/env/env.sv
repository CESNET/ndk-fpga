// env.sv: Verification environment
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Environment for the functional verification.
class env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, DATA_WIDTH, TUSER_WIDTH, STRADDLING) extends uvm_env;
    `uvm_component_param_utils(uvm_ptc_pcie_axi2mfb::env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, DATA_WIDTH, TUSER_WIDTH, STRADDLING));

    uvm_logic_vector_array_axi::env_rx #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING) m_env_rx;
    uvm_logic_vector_array_mfb::env_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)                      m_env_tx;

    uvm_ptc_pcie_axi2mfb::virt_sequencer#(ITEM_WIDTH) vscr;
    uvm_reset::agent m_reset;

    scoreboard#(ITEM_WIDTH) sc;

    // Constructor of the environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of the environment.
    function void build_phase(uvm_phase phase);

        uvm_reset::config_item                    m_config_reset;
        uvm_logic_vector_array_axi::config_item   m_config_rx;
        uvm_logic_vector_array_mfb::config_item   m_config_tx;

        m_config_reset                  = new;
        m_config_reset.active           = UVM_ACTIVE;
        m_config_reset.interface_name   = "vif_reset";

        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        // Passing the virtual interfaces
        m_config_rx                  = new;
        m_config_rx.active           = UVM_ACTIVE;
        m_config_rx.interface_name   = "vif_rx";

        uvm_config_db #(uvm_logic_vector_array_axi::config_item)::set(this, "m_env_rx", "m_config", m_config_rx);
        m_env_rx = uvm_logic_vector_array_axi::env_rx #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING)::type_id::create("m_env_rx", this);

        m_config_tx                  = new;
        m_config_tx.active           = UVM_ACTIVE;
        m_config_tx.interface_name   = "vif_tx";

        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_tx", "m_config", m_config_tx);
        m_env_tx = uvm_logic_vector_array_mfb::env_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)::type_id::create("m_env_tx", this);

        sc     = scoreboard#(ITEM_WIDTH)::type_id::create("sc", this);

        vscr   = uvm_ptc_pcie_axi2mfb::virt_sequencer#(ITEM_WIDTH)::type_id::create("vscr",this);

    endfunction

    // Connect agent's ports with ports from the scoreboard.
    function void connect_phase(uvm_phase phase);

        m_env_rx.analysis_port_data.connect(sc.input_data.analysis_export);

        m_env_tx.analysis_port_data.connect(sc.out_data);

        m_reset.sync_connect(m_env_rx.reset_sync);
        m_reset.sync_connect(m_env_tx.reset_sync);

        vscr.m_reset = m_reset.m_sequencer;
        vscr.m_byte_array_scr = m_env_rx.m_sequencer.m_data;

    endfunction

endclass
