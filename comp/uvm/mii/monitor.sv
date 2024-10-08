/*
 * file       : monitor.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: General MII UVM monitor
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef MII_MONITOR_SV
`define MII_MONITOR_SV

class monitor #(int unsigned CHANNELS, int unsigned WIDTH) extends uvm_monitor;

    // ------------------------------------------------------------------------
    // Registration of monitor to databaze
    `uvm_component_param_utils(uvm_mii::monitor #(CHANNELS, WIDTH))

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(CHANNELS, WIDTH) si;

    // ------------------------------------------------------------------------
    // Reference to the virtual interface
    virtual mii_if #(CHANNELS, WIDTH).monitor vif;

    // ------------------------------------------------------------------------
    // Analysis port used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item #(CHANNELS, WIDTH)) analysis_port;

    // ------------------------------------------------------------------------
    // Constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);

        WHOLE_BYTES : assert((WIDTH & 7) == 0);
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
            si = sequence_item #(CHANNELS, WIDTH)::type_id::create("si");

            si.data = vif.monitor_cb.DATA;
            si.control = vif.monitor_cb.CONTROL;
            si.clk_en = vif.monitor_cb.CLK_EN;

            // Write sequence item to analysis port.
            si.start[this.get_full_name()] = $time();
            analysis_port.write(si);
        end
    endtask

endclass

`endif
