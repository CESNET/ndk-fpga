//-- env.sv: pcie driver to xilinx
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class transaction_info extends uvm_component;
    `uvm_component_param_utils(uvm_pcie::transaction_info);

    uvm_tlm_analysis_fifo #(uvm_pcie::header) fifo_cc;
    uvm_tlm_analysis_fifo #(uvm_pcie::header) fifo_rq;


    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        fifo_cc = new("fifo_cc", this);
        fifo_rq = new("fifo_rq", this);
    endfunction


    task run_phase(uvm_phase phase);
       
        forever begin
            wait (fifo_cc.used() != 0 || fifo_rq.used() != 0);

            if (fifo_cc.used() != 0) begin
                uvm_pcie::header hdr;

                fifo_cc.get(hdr);
                $write("TEST CC %0s\n", hdr.convert2string());
            end

            if (fifo_rq.used() != 0) begin
                uvm_pcie::header hdr;

                fifo_rq.get(hdr);
                $write("TEST CC %0s\n", hdr.convert2string());
            end
    endtask

endclass


