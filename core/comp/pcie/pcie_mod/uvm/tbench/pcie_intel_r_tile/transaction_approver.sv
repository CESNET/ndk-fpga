// transaction_approver.sv: Approves AVST transactions based on credits
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class transaction_approver extends uvm_component;
    `uvm_component_utils(uvm_pcie_intel_r_tile::transaction_approver)

    // Input fifos
    uvm_analysis_export #(uvm_avst_crdt::sequence_item #(2)) avst_crdt_hdr_in [3];
    uvm_analysis_export #(uvm_avst_crdt::sequence_item #(4)) avst_crdt_data_in[3];

    // ---------------------------- //
    // Approval handshake variables //
    // ---------------------------- //

    mailbox #(balance_item) m_mailbox;
    event approve;

    balance_counter m_balance_counter;

    // Constructor
    function new(string name = "transaction_approver", uvm_component parent = null);
        super.new(name, parent);

        m_mailbox = new(1);
        for (int unsigned i = 0; i < 3; i++) begin
            avst_crdt_hdr_in [i] = new($sformatf("avst_crdt_hdr_in_%0d", i), this);
            avst_crdt_data_in[i] = new($sformatf("avst_crdt_data_in%0d", i), this);
        end
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        m_balance_counter = balance_counter::type_id::create("m_balance_counter", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        for (int unsigned i = 0; i < 3; i++) begin
            avst_crdt_hdr_in [i].connect(m_balance_counter.avst_crdt_hdr_in [i].analysis_export);
            avst_crdt_data_in[i].connect(m_balance_counter.avst_crdt_data_in[i].analysis_export);
        end
    endfunction

    task run_phase(uvm_phase phase);
        balance_item cost;

        forever begin
            //wait(m_mailbox.num() == 1);
            m_mailbox.get(cost);
            m_balance_counter.wait_for_init_done();
            m_balance_counter.reduce_balance(cost);
            ->approve;
        end
    endtask

endclass
