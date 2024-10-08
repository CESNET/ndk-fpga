//-- monitor.sv: AXI monitor
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of AXI monitor
class monitor #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS) extends uvm_monitor;

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_param_utils(uvm_axi::monitor #(DATA_WIDTH, TUSER_WIDTH, REGIONS))

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS) si;

    // ------------------------------------------------------------------------
    // Reference to the virtual interface
    virtual axi_if #(DATA_WIDTH, TUSER_WIDTH).monitor vif;

    // ------------------------------------------------------------------------
    // Analysis port used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS)) analysis_port;

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

            si = sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("si");

            // si.tdata  = vif.monitor_cb.TDATA;
            // if (vif.monitor_cb.TREADY && vif.monitor_cb.TVALID) begin
            //     $write("IF AXI TR MON FULL %h\n", vif.monitor_cb.TDATA);
            // end

            for (int unsigned it = 0; it < REGIONS; it++) begin
                si.tdata[it]   = vif.monitor_cb.TDATA[(it+1)*(DATA_WIDTH/REGIONS) - 1 -: (DATA_WIDTH/REGIONS)];
                // if (vif.monitor_cb.TREADY && vif.monitor_cb.TVALID) begin
                //     $write("AXI TDATA MON %h\n", si.tdata[it]);
                // end
            end

            si.tuser  = vif.monitor_cb.TUSER;
            si.tlast  = vif.monitor_cb.TLAST;
            si.tkeep  = vif.monitor_cb.TKEEP;
            si.tvalid = vif.monitor_cb.TVALID;
            si.tready = vif.monitor_cb.TREADY;

            // Write sequence item to analysis port.
            si.start[this.get_full_name()] = $time();
            analysis_port.write(si);
        end
    endtask

endclass
