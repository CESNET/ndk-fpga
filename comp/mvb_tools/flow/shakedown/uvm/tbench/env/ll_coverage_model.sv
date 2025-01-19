// ll_coverage_model.sv: Low-level coverage model for the port activity coverage
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class ll_coverage_model #(int unsigned TX_ITEMS, int unsigned ITEM_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_mvb_shakedown::ll_coverage_model #(TX_ITEMS, ITEM_WIDTH))

    // ------ //
    // Inputs //
    // ------ //

    uvm_tlm_analysis_fifo #(uvm_mvb::sequence_item #(1, ITEM_WIDTH)) in[TX_ITEMS];

    // ----------- //
    // Covergroups //
    // ----------- //

    covergroup port_covergroup(string name = "port_covergroup") with function sample(int unsigned port_count);
        option.name = name;
        option.per_instance = 1;

        // =========== //
        // Coverpoints //
        // =========== //

        port_count : coverpoint port_count
        {
            bins count[] = { [0 : TX_ITEMS] };
        }
    endgroup

    function string convert_to_full_name(string name);
        return { get_full_name(), ".", name };
    endfunction

    function new(string name = "ll_coverage_model", uvm_component parent = null);
        super.new(name, parent);

        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            in[i] = new($sformatf("in_%0d", i), this);
        end

        port_covergroup = new(convert_to_full_name("port_covergroup"));
    endfunction

    task run_phase(uvm_phase phase);
        uvm_mvb::sequence_item #(1, ITEM_WIDTH) in_item;

        forever begin
            int unsigned simultaneously_active_port_count = 0;

            for (int unsigned i = 0; i < TX_ITEMS; i++) begin
                in[i].get(in_item);

                if (in_item.src_rdy === 1'b1 && in_item.dst_rdy === 1'b1 && in_item.vld === 1'b1) begin
                    simultaneously_active_port_count++;
                end
            end

            port_covergroup.sample(simultaneously_active_port_count);
        end
    endtask

endclass
