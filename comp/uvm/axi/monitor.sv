//-- monitor.sv: AXI monitor
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of AXI monitor
class monitor #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_monitor;

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `ndk_component_param_utils(
        uvm_axi::monitor#(ITEMS, ITEM_WIDTH, TUSER_WIDTH),
        $sformatf("uvm_axi::monitor#(%0d,%0d,%0d)",ITEMS, ITEM_WIDTH, TUSER_WIDTH)
    )

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) si;

    // ------------------------------------------------------------------------
    // Reference to the virtual interface
    virtual axi_if #(ITEMS, ITEM_WIDTH, TUSER_WIDTH).monitor vif;

    // ------------------------------------------------------------------------
    // Analysis port used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH)) analysis_port;

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

            si = sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH)::type_id::create("si");

            si.tdata  = vif.monitor_cb.TDATA;
            si.tuser  = vif.monitor_cb.TUSER;
            si.tlast  = vif.monitor_cb.TLAST;
            si.tkeep  = vif.monitor_cb.TKEEP;
            si.tvalid = vif.monitor_cb.TVALID;
            si.tready = vif.monitor_cb.TREADY;

            // Write sequence item to analysis port.
            si.start[this.get_full_name()] = $time;
            analysis_port.write(si);
        end
    endtask

endclass
