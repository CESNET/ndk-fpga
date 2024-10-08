/*
 * file       : monitor.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: PMA monitor
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef PMA_MONITOR_SV
`define PMA_MONITOR_SV

// Definition of MII monitor
class monitor #(int unsigned DATA_WIDTH) extends uvm_monitor;

    `uvm_component_param_utils(uvm_pma::monitor #(DATA_WIDTH))

    sequence_item #(DATA_WIDTH) tr;
    // Reference to the virtual interface, initialized during the connect phase by parent agent.
    virtual pma_if #(DATA_WIDTH).monitor_cb vif;
    // Used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item #(DATA_WIDTH)) analysis_port;

    // Creates new instance of this class.
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    // Instantiates child components.
    function void build_phase(uvm_phase phase);
        analysis_port = new("analysis port", this);
        tr = sequence_item #(DATA_WIDTH)::type_id::create("tr");
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            @(vif.monitor_cb);
            if (vif.monitor_cb.RESET != 1) begin
                tr.data       = vif.monitor_cb.DATA;
                tr.hdr        = vif.monitor_cb.HDR;
                tr.data_vld   = vif.monitor_cb.DATA_VLD;
                tr.hdr_vld    = vif.monitor_cb.HDR_VLD;
                tr.block_lock = vif.monitor_cb.BLOCK_LOCK;
                // Write transaction to analysis port.
                tr.start[this.get_full_name()] = $time();
                analysis_port.write(tr);
            end
        end
    endtask

endclass

`endif
