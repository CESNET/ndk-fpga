//-- monitor.sv: AVST credit control monitor
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

// Definition of AVST credit control monitor
class monitor extends uvm_monitor;

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_utils(uvm_crdt::monitor)

    // ------------------------------------------------------------------------
    // Variables
    sequence_item si;

    // ------------------------------------------------------------------------
    // Reference to the virtual interface
    virtual crdt_if.monitor vif;
    
    // ------------------------------------------------------------------------
    // Analysis port used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item) analysis_port;

    // ------------------------------------------------------------------------
    // Constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Functions
    function void build_phase(uvm_phase phase);
        analysis_port = new("analysis port", this);
    endfunction

    task run_phase(uvm_phase phase);
        int cnt = 0;
        forever begin
            @(vif.monitor_cb);

            si = sequence_item::type_id::create("si");

            si.init_done = vif.monitor_cb.INIT_DONE;
            si.update    = vif.monitor_cb.UPDATE;
            si.cnt_ph    = vif.monitor_cb.CNT_PH;
            si.cnt_nph   = vif.monitor_cb.CNT_NPH;
            si.cnt_cplh  = vif.monitor_cb.CNT_CPLH;
            si.cnt_pd    = vif.monitor_cb.CNT_PD;
            si.cnt_npd   = vif.monitor_cb.CNT_NPD;
            si.cnt_cpld  = vif.monitor_cb.CNT_CPLD;

            // Write sequence item to analysis port.
            analysis_port.write(si);
        end
    endtask

endclass
