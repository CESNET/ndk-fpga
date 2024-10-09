// env.sv: Environment for Intel R-Tile device
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, AVST_DOWN_META_W, CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, AVST_UP_META_W) extends uvm_pcie_intel::env #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, AVST_DOWN_META_W, CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, AVST_UP_META_W);
    `uvm_component_param_utils(uvm_pcie_intel_r_tile::env #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, AVST_DOWN_META_W, CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, AVST_UP_META_W));

    uvm_avst_crdt::agent_rx_hdr  m_avst_crdt_up_hdr [3];
    uvm_avst_crdt::agent_rx_data m_avst_crdt_up_data[3];

    uvm_avst_crdt::agent_tx_hdr  m_avst_crdt_down_hdr [3];
    uvm_avst_crdt::agent_tx_data m_avst_crdt_down_data[3];

    transaction_approver m_transaction_approver;
    transaction_checker #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, AVST_UP_META_W, 3) m_transaction_checker;
    valuer #(AVST_UP_META_W) m_valuer;
    balance_splitter m_balance_splitter;

    function new(string name = "env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_pcie::config_item m_config;

        if(!uvm_config_db #(uvm_pcie::config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "\n\tUnable to get configuration object");
        end

        uvm_pcie_intel::driver::type_id::set_inst_override(
            uvm_pcie_intel_r_tile::driver::get_type(),
            "m_driver",
            this
        );
        for (int unsigned i = 0; i < 3; i++) begin
            uvm_avst_crdt::sequencer #(2)::type_id::set_inst_override(
                uvm_pcie_intel_r_tile::sequencer #(2)::get_type(),
                $sformatf("m_avst_crdt_up_hdr_%0d.m_sequencer", i),
                this
            );
            uvm_avst_crdt::sequencer #(4)::type_id::set_inst_override(
                uvm_pcie_intel_r_tile::sequencer #(4)::get_type(),
                $sformatf("m_avst_crdt_up_data_%0d.m_sequencer", i),
                this
            );
        end

        super.build_phase(phase);

        for (int unsigned i = 0; i < 3; i++) begin
            uvm_avst_crdt::config_item m_avst_crdt_up_hdr_cfg;
            uvm_avst_crdt::config_item m_avst_crdt_up_data_cfg;
            uvm_avst_crdt::config_item m_avst_crdt_down_hdr_cfg;
            uvm_avst_crdt::config_item m_avst_crdt_down_data_cfg;

            // UP HDR
            m_avst_crdt_up_hdr_cfg = new();
            m_avst_crdt_up_hdr_cfg.active = UVM_ACTIVE;
            m_avst_crdt_up_hdr_cfg.interface_name = $sformatf("%s_crdt_up_hdr_%0d", m_config.interface_name, i);
            m_avst_crdt_up_hdr[i] = uvm_avst_crdt::agent_rx_hdr::type_id::create($sformatf("m_avst_crdt_up_hdr_%0d", i), this);
            uvm_config_db #(uvm_avst_crdt::config_item)::set(this, $sformatf("m_avst_crdt_up_hdr_%0d", i), "m_config", m_avst_crdt_up_hdr_cfg);

            // UP DATA
            m_avst_crdt_up_data_cfg = new();
            m_avst_crdt_up_data_cfg.active = UVM_ACTIVE;
            m_avst_crdt_up_data_cfg.interface_name = $sformatf("%s_crdt_up_data_%0d", m_config.interface_name, i);
            m_avst_crdt_up_data[i] = uvm_avst_crdt::agent_rx_data::type_id::create($sformatf("m_avst_crdt_up_data_%0d", i), this);
            uvm_config_db #(uvm_avst_crdt::config_item)::set(this, $sformatf("m_avst_crdt_up_data_%0d", i), "m_config", m_avst_crdt_up_data_cfg);

            // DOWN HDR
            m_avst_crdt_down_hdr_cfg = new();
            m_avst_crdt_down_hdr_cfg.active = UVM_ACTIVE;
            m_avst_crdt_down_hdr_cfg.interface_name = $sformatf("%s_crdt_down_hdr_%0d", m_config.interface_name, i);
            m_avst_crdt_down_hdr[i] = uvm_avst_crdt::agent_tx_hdr::type_id::create($sformatf("m_avst_crdt_down_hdr_%0d", i), this);
            uvm_config_db #(uvm_avst_crdt::config_item)::set(this, $sformatf("m_avst_crdt_down_hdr_%0d", i), "m_config", m_avst_crdt_down_hdr_cfg);

            // DOWN DATA
            m_avst_crdt_down_data_cfg = new();
            m_avst_crdt_down_data_cfg.active = UVM_ACTIVE;
            m_avst_crdt_down_data_cfg.interface_name = $sformatf("%s_crdt_down_data_%0d", m_config.interface_name, i);
            m_avst_crdt_down_data[i] = uvm_avst_crdt::agent_tx_data::type_id::create($sformatf("m_avst_crdt_down_data_%0d", i), this);
            uvm_config_db #(uvm_avst_crdt::config_item)::set(this, $sformatf("m_avst_crdt_down_data_%0d", i), "m_config", m_avst_crdt_down_data_cfg);
        end

        m_transaction_approver = transaction_approver::type_id::create("m_transaction_approver", this);
        m_valuer = valuer #(AVST_UP_META_W)::type_id::create("m_valuer", this);
        m_balance_splitter = balance_splitter::type_id::create("m_balance_splitter", this);
        
        // THE CURRENT IMPLEMENTATION OF PCIE-TOP DOES NOT TAKE INTO ACCOUNT UP-SIDE CREDITS SENT FROM VERIFICATION
        // UNCOMMENT BELOW IF YOU WANT TO ENABLE CHECKING OF THIS FEATURE
        // m_transaction_checker = transaction_checker #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, AVST_UP_META_W, 3)::type_id::create("m_transaction_checker", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // Approver on DOWN
        uvm_config_db #(mailbox #(balance_item))::set(this, "m_driver", "mailbox", m_transaction_approver.m_mailbox);
        uvm_config_db #(event)                  ::set(this, "m_driver", "approve", m_transaction_approver.approve);
        for (int unsigned i = 0; i < 3; i++) begin
            m_avst_crdt_down_hdr [i].analysis_port.connect(m_transaction_approver.avst_crdt_hdr_in [i].analysis_export);
            m_avst_crdt_down_data[i].analysis_port.connect(m_transaction_approver.avst_crdt_data_in[i].analysis_export);
        end

        // THE CURRENT IMPLEMENTATION OF PCIE-TOP DOES NOT TAKE INTO ACCOUNT UP-SIDE CREDITS SENT FROM VERIFICATION
        // UNCOMMENT BELOW IF YOU WANT TO ENABLE CHECKING OF THIS FEATURE
        // // Checker on UP
        // m_avst_up.m_avst_agent.analysis_port.connect(m_transaction_checker.avst_in.analysis_export);
        // for (int unsigned i = 0; i < 3; i++) begin
        //     m_avst_crdt_up_hdr [i].analysis_port.connect(m_transaction_checker.avst_crdt_hdr_in [i].analysis_export);
        //     m_avst_crdt_up_data[i].analysis_port.connect(m_transaction_checker.avst_crdt_data_in[i].analysis_export);
        // end

        // Sequence returning credits on UP
        m_avst_up.analysis_port_meta.connect(m_valuer.analysis_export);
        m_valuer.analysis_port.connect(m_balance_splitter.analysis_export);

        for (int unsigned i = 0; i < 3; i++) begin
            sequencer #(2) cast_sequencer;

            assert($cast(cast_sequencer, m_avst_crdt_up_hdr[i].m_sequencer))
            else begin
                `uvm_fatal(this.get_full_name(), "\n\tCast failed")
            end
            reset_sync.push_back(cast_sequencer.reset_sync);

            m_balance_splitter.analysis_port[i].connect(cast_sequencer.analysis_export);
        end

        for (int unsigned i = 0; i < 3; i++) begin
            sequencer #(4) cast_sequencer;

            assert($cast(cast_sequencer, m_avst_crdt_up_data[i].m_sequencer))
            else begin
                `uvm_fatal(this.get_full_name(), "\n\tCast failed")
            end
            reset_sync.push_back(cast_sequencer.reset_sync);

            m_balance_splitter.analysis_port[i+3].connect(cast_sequencer.analysis_export);
        end
    endfunction

    task run_phase(uvm_phase phase);
        // Credit initialization sequences
        uvm_avst_crdt::sequence_rx_initializing_hdr  m_crdt_up_hdr_sequence_init [3];
        uvm_avst_crdt::sequence_rx_initializing_data m_crdt_up_data_sequence_init[3];

        uvm_avst_crdt::sequence_tx_ack_hdr  m_crdt_down_hdr_sequence_init_ack [3];
        uvm_avst_crdt::sequence_tx_ack_data m_crdt_down_data_sequence_init_ack[3];

        // Credit transaction sequence
        sequence_returning_hdr  m_crdt_up_hdr_sequence_returning [3];
        sequence_returning_data m_crdt_up_data_sequence_returning[3];

        // AVST sequences
        uvm_pcie_intel::sequence_data                     seq_data;
        uvm_pcie_intel::sequence_meta #(AVST_DOWN_META_W) seq_meta;
        uvm_avst::sequence_lib_tx #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, AVST_UP_META_W) seq_up_rdy;
        
        for (int unsigned i = 0; i < 3; i++) begin
            m_crdt_up_hdr_sequence_init [i] = uvm_avst_crdt::sequence_rx_initializing_hdr::type_id::create($sformatf("m_crdt_up_hdr_sequence_init_%0d", i));
            m_crdt_up_data_sequence_init[i] = uvm_avst_crdt::sequence_rx_initializing_data::type_id::create($sformatf("m_crdt_up_data_sequence_init_%0d", i));

            m_crdt_down_hdr_sequence_init_ack [i] = uvm_avst_crdt::sequence_tx_ack_hdr::type_id::create($sformatf("m_crdt_down_hdr_sequence_init_ack_%0d", i));
            m_crdt_down_data_sequence_init_ack[i] = uvm_avst_crdt::sequence_tx_ack_data::type_id::create($sformatf("m_crdt_down_data_sequence_init_ack_%0d", i));

            m_crdt_up_hdr_sequence_returning [i] = sequence_returning_hdr::type_id::create($sformatf("m_crdt_up_hdr_sequence_returning_%0d", i));
            m_crdt_up_data_sequence_returning[i] = sequence_returning_data::type_id::create($sformatf("m_crdt_up_data_sequence_returning_%0d", i));
        end

        seq_data = uvm_pcie_intel::sequence_data::type_id::create("seq_data");
        assert(seq_data.randomize())
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot randomize data sequence")
        end

        seq_meta = uvm_pcie_intel::sequence_meta #(AVST_DOWN_META_W)::type_id::create("seq_meta");
        assert(seq_meta.randomize())
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot randomize meta sequence")
        end

        seq_up_rdy = uvm_avst::sequence_lib_tx #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, AVST_UP_META_W)::type_id::create("seq_up_rdy");
        seq_up_rdy.init_sequence();
        seq_up_rdy.min_random_count = 100;
        seq_up_rdy.max_random_count = 200;

        // Credit initialization
        for (int unsigned i = 0; i < 3; i++) begin
            fork
                int unsigned j = i;

                begin
                    assert(m_crdt_up_hdr_sequence_init[j].randomize());
                    m_crdt_up_hdr_sequence_init[j].start(m_avst_crdt_up_hdr[j].m_sequencer);
                end
                begin
                    assert(m_crdt_up_data_sequence_init[j].randomize());
                    m_crdt_up_data_sequence_init[j].start(m_avst_crdt_up_data[j].m_sequencer);
                end

                begin
                    assert(m_crdt_down_hdr_sequence_init_ack[j].randomize());
                    m_crdt_down_hdr_sequence_init_ack[j].start(m_avst_crdt_down_hdr[j].m_sequencer);
                end
                begin
                    assert(m_crdt_down_data_sequence_init_ack[j].randomize());
                    m_crdt_down_data_sequence_init_ack[j].start(m_avst_crdt_down_data[j].m_sequencer);
                end
            join_none
        end

        wait fork; // End of initialization

        // Credit transactions
        for (int unsigned i = 0; i < 3; i++) begin
            fork
                int unsigned j = i;
                
                forever begin
                    assert(m_crdt_up_hdr_sequence_returning[j].randomize());
                    m_crdt_up_hdr_sequence_returning[j].start(m_avst_crdt_up_hdr[j].m_sequencer);
                end
                forever begin
                    assert(m_crdt_up_data_sequence_returning[j].randomize());
                    m_crdt_up_data_sequence_returning[j].start(m_avst_crdt_up_data[j].m_sequencer);
                end
            join_none;
        end

        // AVST data/meta transactions
        fork
            seq_data.start(m_avst_down.m_sequencer.m_data);
            seq_meta.start(m_avst_down.m_sequencer.m_meta);

            forever begin
                assert(seq_up_rdy.randomize());
                seq_up_rdy.start(m_avst_up.m_sequencer);
            end
        join;
    endtask

endclass
