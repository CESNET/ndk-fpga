// env.sv: Verification environment
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Vladislav Valek <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class mfb_to_lbus_seqv_lib #(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE, META_WIDTH) extends uvm_byte_array_mfb::sequence_lib_rx#(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE, META_WIDTH);
  `uvm_object_param_utils(    uvm_mfb_to_lbus_adapter::mfb_to_lbus_seqv_lib#(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE, META_WIDTH))
  `uvm_sequence_library_utils(uvm_mfb_to_lbus_adapter::mfb_to_lbus_seqv_lib#(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE, META_WIDTH))

  function new(string name = "");
    super.new(name);
    init_sequence_library();
  endfunction

    virtual function void init_sequence(uvm_byte_array_mfb::config_sequence param_cfg = null);
        //super.init_sequence(param_cfg);
        if (param_cfg == null) begin
            this.cfg = new();
        end else begin
            this.cfg = param_cfg;
        end
        this.add_sequence(uvm_byte_array_mfb::seqv_no_inframe_gap_rx #(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE, META_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_mfb::sequence_full_speed_rx #(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE, META_WIDTH)::get_type());
    endfunction

endclass



// Environment for the functional verification.
class env #(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE, TX_REGIONS, TX_REGION_SIZE, TX_BLOCK_SIZE) extends uvm_env;
    `uvm_component_param_utils(uvm_mfb_to_lbus_adapter::env #(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE, TX_REGIONS, TX_REGION_SIZE, TX_BLOCK_SIZE));

    uvm_byte_array_mfb::env_rx #(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE, 0) m_env_rx;
    uvm_byte_array_mfb::env_tx #(TX_REGIONS, TX_REGION_SIZE, TX_BLOCK_SIZE, 0) m_env_tx;

    uvm_mfb_to_lbus_adapter::virt_sequencer vscr;
    uvm_reset::agent m_reset;

    scoreboard sc;

    // Constructor of the environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of the environment.
    function void build_phase(uvm_phase phase);

        uvm_reset::config_item            m_config_reset;
        uvm_byte_array_mfb::config_item   m_config_rx;
        uvm_byte_array_mfb::config_item   m_config_tx;

        //change implementation
        uvm_byte_array_mfb::sequence_lib_rx#(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE, 0)::type_id::set_inst_override(uvm_mfb_to_lbus_adapter::mfb_to_lbus_seqv_lib#(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE, 0)::get_type(),
             {this.get_full_name(), ".m_env_rx.mfb_seq"});


        m_config_reset                  = new;
        m_config_reset.active           = UVM_ACTIVE;
        m_config_reset.interface_name   = "vif_reset";

        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        // Passing the virtual interfaces
        m_config_rx                  = new;
        m_config_rx.active           = UVM_ACTIVE;
        m_config_rx.interface_name   = "vif_rx";
        m_config_rx.meta_behav       = uvm_byte_array_mfb::config_item::META_SOF;

        uvm_config_db #(uvm_byte_array_mfb::config_item)::set(this, "m_env_rx", "m_config", m_config_rx);
        m_env_rx = uvm_byte_array_mfb::env_rx#(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE,0)::type_id::create("m_env_rx", this);

        m_config_tx                  = new;
        m_config_tx.active           = UVM_ACTIVE;
        m_config_tx.interface_name   = "vif_tx";
        m_config_tx.meta_behav       = uvm_byte_array_mfb::config_item::META_SOF;

        uvm_config_db #(uvm_byte_array_mfb::config_item)::set(this, "m_env_tx", "m_config", m_config_tx);
        m_env_tx = uvm_byte_array_mfb::env_tx#(TX_REGIONS, TX_REGION_SIZE, TX_BLOCK_SIZE, 0)::type_id::create("m_env_tx", this);

        sc     = scoreboard::type_id::create("sc", this);
        vscr   = uvm_mfb_to_lbus_adapter::virt_sequencer::type_id::create("vscr",this);

    endfunction

    // Connect agent's ports with ports from the scoreboard.
    function void connect_phase(uvm_phase phase);

        m_env_rx.m_byte_array_agent.analysis_port.connect(sc.input_data);

        m_env_tx.m_byte_array_agent.analysis_port.connect(sc.out_data);

        m_reset.sync_connect(m_env_rx.reset_sync);
        m_reset.sync_connect(m_env_tx.reset_sync);

        vscr.m_reset = m_reset.m_sequencer;
        vscr.m_byte_array_scr = m_env_rx.m_sequencer.m_data;


    endfunction

endclass
