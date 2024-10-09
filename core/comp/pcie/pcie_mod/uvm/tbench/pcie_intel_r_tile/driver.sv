// driver.sv: Driver for Intel R-Tile device
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class driver extends uvm_pcie_intel::driver;
    `uvm_component_param_utils(uvm_pcie_intel_r_tile::driver);

    localparam int unsigned HDR_WIDTH    = 128;
    localparam int unsigned PREFIX_WIDTH = 32;

    mailbox #(balance_item) m_mailbox;
    event approve;

    function new(string name = "driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);

        assert(uvm_config_db #(uvm_pcie_intel::req_fifo #(uvm_pcie::header))::get(this, "", "seq_fifo_data", fifo_data))
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot get request header fifo");
        end
        assert(uvm_config_db #(uvm_pcie_intel::req_fifo #(uvm_pcie::header))::get(this, "", "seq_fifo_meta", fifo_meta))
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot get request header fifo");
        end

        assert(uvm_config_db #(mailbox #(balance_item))::get(this, "", "mailbox", m_mailbox))
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot get mailbox");
        end
        assert(uvm_config_db #(event)::get(this, "", "approve", approve))
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot get approve event");
        end
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);

            wait((fifo_meta.size() == 0 || fifo_data.size()) && fifo_meta.size() < 10 || fifo_data.size() < 10);

            wait_for_approval(req);

            fifo_meta.push_back(req);
            fifo_data.push_back(req);

            seq_item_port.item_done();
        end
    endtask

    task wait_for_approval(uvm_pcie::header header);
        balance_item cost = get_transaction_cost(header);
        m_mailbox.put(cost);
        wait(approve.triggered);
    endtask

    function balance_item get_transaction_cost(uvm_pcie::header header);
        balance_item cost;

        logic [3 -1 : 0] fmt       = header.fmt;
        logic [5 -1 : 0] pcie_type = header.pcie_type;
        logic [10-1 : 0] length    = header.length;

        cost = balance_item::type_id::create("cost");

        // Completion with Data
        if ({ fmt, pcie_type } === 8'b01001010) begin
            cost.header.cpl = 1;
            cost.data  .cpl = get_data_cost(header.length_get());
        end
        // Request with Data
        else if (fmt[2 : 1] === 2'b01) begin
            cost.header.p = 1;
            cost.data  .p = get_data_cost(header.length_get());
        end
        // Request without Data
        else begin
            cost.header.np = 1;
        end

        return cost;
    endfunction

    function int unsigned get_data_cost(logic [10-1 : 0] length);
        return ((length - 1) / 4) + 1; // TLP length => credit value
    endfunction

endclass
