/*
 * file       : monitor.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: monitor mi interface and send data to subscribers
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class monitor #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_monitor;

    `uvm_component_param_utils(uvm_mi::monitor #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    // Reference to the virtual interface, initialized during the connect phase by parent agent.
    virtual mi_if #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH).monitor vif;
    // variables
    sequence_item_request #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) request;
    sequence_item_response #(DATA_WIDTH)                         response;
    // analysis_ports
    uvm_analysis_port #(sequence_item_request #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)) analysis_port_rq;
    uvm_analysis_port #(sequence_item_response #(DATA_WIDTH))                         analysis_port_rs;

    // Creates new instance of this class.
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    // Instantiates child components.
    function void build_phase(uvm_phase phase);
        analysis_port_rq = new("analysis_port_rq", this);
        analysis_port_rs = new("analysis_port_rs", this);
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            request = sequence_item_request#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("monitor_rq");
            response = sequence_item_response#(DATA_WIDTH)::type_id::create("monitor_rs");

            @(vif.monitor_cb);
            //send request
            request.start[this.get_full_name()] = $time();
            request.addr = vif.monitor_cb.ADDR;
            request.be   = vif.monitor_cb.BE;
            request.wr   = vif.monitor_cb.WR;
            request.dwr  = vif.monitor_cb.DWR;
            request.meta  = vif.monitor_cb.META;
            request.rd   = vif.monitor_cb.RD;
            request.ardy = vif.monitor_cb.ARDY;
            analysis_port_rq.write(request);

            //send response
            response.start[this.get_full_name()] = $time();
            response.drd  = vif.monitor_cb.DRD;
            response.ardy = vif.monitor_cb.ARDY;
            response.drdy = vif.monitor_cb.DRDY;
            analysis_port_rs.write(response);
        end
    endtask

endclass

