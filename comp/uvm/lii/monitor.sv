/*
 * file       : monitor.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII monitor
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef LII_MONITOR_SV
`define LII_MONITOR_SV

// Definition of LII monitor
class monitor #(int unsigned DATA_WIDTH, logic FAST_SOF, int unsigned META_WIDTH, int unsigned SOF_WIDTH) extends uvm_monitor;

    `uvm_component_param_utils(uvm_lii::monitor #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH))

    sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH) tr;
    // Reference to the virtual interface, initialized during the connect phase by parent agent.
    virtual lii_if #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH).monitor_cb vif;
    // Used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)) analysis_port;

    // Creates new instance of this class.
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    // Instantiates child components.
    function void build_phase(uvm_phase phase);
        analysis_port = new("analysis port", this);
        tr = sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)::type_id::create("tr");
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            @(vif.monitor_cb);
            if(vif.monitor_cb.RESET != 1) begin
                tr.data        = vif.monitor_cb.DATA;
                tr.bytes_vld   = vif.monitor_cb.BYTES_VLD;
                tr.sof         = vif.monitor_cb.SOF;
                tr.eof         = vif.monitor_cb.EOF;
                tr.rdy         = vif.monitor_cb.RDY;
                tr.eeof        = vif.monitor_cb.EEOF;
                tr.edb         = vif.monitor_cb.EDB;
                tr.link_status = vif.monitor_cb.LINK_STATUS;
                tr.meta        = vif.monitor_cb.META;
                tr.rxdecerr    = vif.monitor_cb.RXDECERR;
                tr.rxseqerr    = vif.monitor_cb.RXSEQERR;
                tr.crcerr      = vif.monitor_cb.CRCERR;
                // Write transaction to analysis port.
                tr.start[this.get_full_name()] = $time();
                analysis_port.write(tr);
            end
        end
    endtask

endclass

`endif
