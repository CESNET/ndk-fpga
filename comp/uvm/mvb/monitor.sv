//-- monitor.sv: Mvb monitor
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_MONITOR_SV
`define MVB_MONITOR_SV

// Definition of mvb monitor
class monitor #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_monitor;

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_param_utils(uvm_mvb::monitor #(ITEMS, ITEM_WIDTH))

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(ITEMS, ITEM_WIDTH) si;

    // ------------------------------------------------------------------------
    // Reference to the virtual interface
    virtual mvb_if #(ITEMS, ITEM_WIDTH).monitor vif;

    // ------------------------------------------------------------------------
    // Analysis port used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item #(ITEMS, ITEM_WIDTH)) analysis_port;

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
        forever begin
            @(vif.monitor_cb);

            // Capture actual data at interface
	        si = sequence_item #(ITEMS, ITEM_WIDTH)::type_id::create("si");
            for (int i = 0 ; i < ITEMS ; i++ ) begin
                si.data[i] = vif.monitor_cb.DATA[(i+1)*ITEM_WIDTH - 1 -: ITEM_WIDTH];
            end

            si.start[this.get_full_name()] = $time();
            si.vld      = vif.monitor_cb.VLD;
            si.src_rdy  = vif.monitor_cb.SRC_RDY;
            si.dst_rdy  = vif.monitor_cb.DST_RDY;

            // Write sequence item to analysis port.
            analysis_port.write(si);

        end
    endtask

endclass

`endif
