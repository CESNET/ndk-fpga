// transaction_checker.sv: Checks AVST transaction's validity based on credits
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class transaction_checker #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY) extends uvm_component;
    `uvm_component_param_utils(uvm_pcie_intel_r_tile::transaction_checker #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY))

    localparam int unsigned HDR_WIDTH    = 128;
    localparam int unsigned PREFIX_WIDTH = 32;

    // Inputs
    uvm_tlm_analysis_fifo #(uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)) avst_in;

    uvm_tlm_analysis_fifo #(uvm_avst_crdt::sequence_item #(2)) avst_crdt_hdr_in [3];
    uvm_tlm_analysis_fifo #(uvm_avst_crdt::sequence_item #(4)) avst_crdt_data_in[3];

    balance_counter m_balance_counter;

    // AVST items => logic vector items => balance items converting logic
    protected uvm_logic_vector_array_avst::monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY) m_monitor;
    protected valuer #(META_WIDTH) m_valuer;
    protected uvm_tlm_analysis_fifo #(balance_item) cost_fifo;

    // Constructor
    function new(string name = "transaction_checker", uvm_component parent = null);
        super.new(name, parent);

        avst_in   = new("avst_in", this);
        cost_fifo = new("cost_fifo", this);

        for (int unsigned i = 0; i < 3; i++) begin
            avst_crdt_hdr_in [i] = new($sformatf("avst_crdt_hdr_in_%0d", i), this);
            avst_crdt_data_in[i] = new($sformatf("avst_crdt_data_in_%0d", i), this);
        end
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        m_balance_counter = balance_counter::type_id::create("m_balance_counter", this);
        m_valuer = valuer #(META_WIDTH)::type_id::create("m_valuer", this);
        m_monitor = uvm_logic_vector_array_avst::monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)::type_id::create("m_monitor", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        m_monitor.analysis_port.connect(m_valuer.analysis_export);
        m_valuer.analysis_port.connect(cost_fifo.analysis_export);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) avst_item;

        uvm_avst_crdt::sequence_item #(2) avst_crdt_hdr_item [3];
        uvm_avst_crdt::sequence_item #(4) avst_crdt_data_item[3];

        balance_item total_cost;
        balance_item item_cost;

        total_cost = balance_item::type_id::create("total_cost");

        forever begin
            avst_in.get(avst_item);

            for (int unsigned i = 0; i < 3; i++) begin
                avst_crdt_hdr_in [i].get(avst_crdt_hdr_item [i]);
                avst_crdt_data_in[i].get(avst_crdt_data_item[i]);
            end

            total_cost.reset();

            // Write AVST item to monitor
            m_monitor.write(avst_item);
            while (cost_fifo.used() > 0) begin // Get all balance items
                cost_fifo.get(item_cost);

                total_cost.header.p   += item_cost.header.p;
                total_cost.header.np  += item_cost.header.np;
                total_cost.header.cpl += item_cost.header.cpl;
                total_cost.data.p     += item_cost.data.p;
                total_cost.data.np    += item_cost.data.np;
                total_cost.data.cpl   += item_cost.data.cpl;
            end

            if (!total_cost.is_zero()) begin
                assert(m_balance_counter.is_init_done())
                else begin
                    `uvm_error(this.get_full_name(), "\n\tUser can't send the transaction while initializing phase is in progress!")
                end
                assert(m_balance_counter.try_reduce_balance(total_cost))
                else begin
                    `uvm_error(this.get_full_name(), "\n\tUser has insufficient number of credits to send the transaction!")
                end
            end

            for (int unsigned i = 0; i < 3; i++) begin
                m_balance_counter.avst_crdt_hdr_in [i].write(avst_crdt_hdr_item [i]);
                m_balance_counter.avst_crdt_data_in[i].write(avst_crdt_data_item[i]);
            end
        end
    endtask

endclass
