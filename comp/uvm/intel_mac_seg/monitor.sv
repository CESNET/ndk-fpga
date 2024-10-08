/*
 * file       : monitor.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Intel mac seq monitor
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

// Definition of mvb monitor
class monitor #(int unsigned SEGMENTS) extends uvm_monitor;
    `uvm_component_param_utils(uvm_intel_mac_seg::monitor#(SEGMENTS))

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(SEGMENTS) tr;

    // ------------------------------------------------------------------------
    // Reference to the virtual interface
    virtual intel_mac_seg_if #(SEGMENTS).monitor vif;

    // ------------------------------------------------------------------------
    // Analysis port used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item #(SEGMENTS)) analysis_port;

    // ------------------------------------------------------------------------
    // Constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Functions
    function void build_phase(uvm_phase phase);
        analysis_port = new("analysis_port", this);
        tr = sequence_item #(SEGMENTS)::type_id::create("tr");
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            @(vif.monitor_cb);

            // Capture actual data at interface
            {<<64{tr.data}}       =  vif.monitor_cb.DATA;
            {<<1{tr.inframe}}     =  vif.monitor_cb.INFRAME;
            {<<3{tr.eop_empty}}   =  vif.monitor_cb.EOP_EMPTY;
            {<<1{tr.fcs_error}}   =  vif.monitor_cb.FCS_ERROR;
            {<<2{tr.error}}       =  vif.monitor_cb.ERROR;
            {<<3{tr.status_data}} =  vif.monitor_cb.STATUS_DATA;
            tr.valid              =  vif.monitor_cb.VALID;
            tr.ready              =  vif.monitor_cb.READY;

            // Write sequence item to analysis port.
            tr.start[this.get_full_name()] = $time();
            analysis_port.write(tr);
        end
    endtask

endclass

