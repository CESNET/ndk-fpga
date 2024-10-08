// driver.sv: pcie driver for converting to xilinx
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause



class driver extends uvm_pcie::driver;
    `uvm_component_param_utils(uvm_pcie_xilinx::driver);

    //SEND DATA
    protected req_fifo#(uvm_pcie::request_header)   fifo_cq;
    protected req_fifo#(uvm_pcie::completer_header) fifo_rc;


    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction


    task run_phase(uvm_phase phase);

        assert(uvm_config_db #(req_fifo#(uvm_pcie::request_header)  )::get(this, "", "seq_fifo_cq", fifo_cq)) else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot get requeste header fifo");
        end
        assert(uvm_config_db #(req_fifo#(uvm_pcie::completer_header))::get(this, "", "seq_fifo_rc", fifo_rc)) else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot get completer header fifo");
        end


        forever begin
            seq_item_port.get_next_item(req);
            //seq_item_port.try_next_item(req);

            //CQ header
            if (req.hdr_type == uvm_pcie::header::RQ_HDR) begin
                uvm_pcie::request_header rq_hdr;

                assert($cast(rq_hdr, req)) else begin
                    `uvm_fatal(this.get_full_name(), "Cannot cast to request header");
                end

                wait(fifo_cq.size() == 0);
                fifo_cq.push_back(rq_hdr);
            //RC header
            end else if (req.hdr_type == uvm_pcie::header::COMPLETER_HDR) begin
                uvm_pcie::completer_header compl_hdr;

                assert($cast(compl_hdr, req)) else begin
                    `uvm_fatal(this.get_full_name(), "Cannot cast to completer header");
                end

                wait(fifo_rc.size() == 0);
                fifo_rc.push_back(compl_hdr);
            end

            seq_item_port.item_done();
        end
    endtask

endclass

