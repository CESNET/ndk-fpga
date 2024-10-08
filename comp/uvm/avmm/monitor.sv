// monitor.sv: AVMM monitor
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class monitor #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_monitor;
    `uvm_component_param_utils(uvm_avmm::monitor #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // --------- //
    // Variables //
    // --------- //

    // Reference to the virtual interface
    virtual avmm_if #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH).monitor vif;

    // Analysis ports
    uvm_analysis_port #(sequence_item_request  #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)) analysis_port_request;
    uvm_analysis_port #(sequence_item_response #(DATA_WIDTH))                             analysis_port_response;

    // Constructor
    function new (string name = "monitor", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // --------- //
    // Functions //
    // --------- //

    function void build_phase(uvm_phase phase);
        analysis_port_request  = new("analysis_port_request",  this);
        analysis_port_response = new("analysis_port_response", this);
    endfunction

    task run_phase(uvm_phase phase);
        sequence_item_request  #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) request;
        sequence_item_response #(DATA_WIDTH)                             response;

        forever begin
            @(vif.monitor_cb);

            // Send request
            request = sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("request");
            request.ready      = vif.monitor_cb.READY;
            request.read       = vif.monitor_cb.READ;
            request.write      = vif.monitor_cb.WRITE;
            request.address    = vif.monitor_cb.ADDRESS;
            request.writedata  = vif.monitor_cb.WRITEDATA;
            request.burstcount = vif.monitor_cb.BURSTCOUNT;
            // Write sequence item to analysis port
            request.start[this.get_full_name()] = $time();
            analysis_port_request.write(request);

            // Send response
            response = sequence_item_response #(DATA_WIDTH)::type_id::create("response");
            response.readdata      = vif.monitor_cb.READDATA;
            response.readdatavalid = vif.monitor_cb.READDATAVALID;
            // Write sequence item to analysis port
            response.start[this.get_full_name()] = $time();
            analysis_port_response.write(response);
        end
    endtask

endclass
