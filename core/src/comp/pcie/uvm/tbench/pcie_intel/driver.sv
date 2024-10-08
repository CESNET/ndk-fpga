// env.sv: pcie driver for intel
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class driver extends uvm_pcie::driver;
    `uvm_component_param_utils(uvm_pcie_intel::driver);

    //SEND DATA
    protected req_fifo#(uvm_pcie::header)   fifo_data;
    protected req_fifo#(uvm_pcie::header)   fifo_meta;


    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction


    task run_phase(uvm_phase phase);

        assert(uvm_config_db #(req_fifo#(uvm_pcie::header)  )::get(this, "", "seq_fifo_data", fifo_data)) else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot get requeste header fifo");
        end
        assert(uvm_config_db #(req_fifo#(uvm_pcie::header)  )::get(this, "", "seq_fifo_meta", fifo_meta)) else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot get requeste header fifo");
        end

        forever begin
            seq_item_port.get_next_item(req);
            //seq_item_port.try_next_item(req);

            wait((fifo_meta.size() == 0 || fifo_data.size()) && fifo_meta.size() < 10 || fifo_data.size() < 10);
            fifo_meta.push_back(req);
            fifo_data.push_back(req);

            seq_item_port.item_done();
        end
    endtask
endclass
