// property.sv: Properties for AVMM interface
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef AVMM_PROPERTY
`define AVMM_PROPERTY

`include "uvm_macros.svh"
import uvm_pkg::*;

module avmm_property #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH)
    (
        input RESET,
        avmm_if vif
    );
    string module_name = "";
    logic START = 1'b1;

    // Start check properties after first clock
    initial begin
        $sformat(module_name, "%m");
        @(posedge vif.CLK)
        #(10ps)
        START = 1'b0;
    end

    // ---------- //
    // Properties //
    // ---------- //

    // Read and Write simultaneously
    property read_and_write_simultaneously;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        !(vif.READ && vif.WRITE);
    endproperty

    // READY must be always valid
    property ready_undefined;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        !$isunknown(vif.READY);
    endproperty

    // READDATAVALID must be always valid
    property readdatavalid_undefined;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        !$isunknown(vif.READDATAVALID);
    endproperty

    // ---------- //
    // Assertions //
    // ---------- //

    assert property (read_and_write_simultaneously)
    else begin
        `uvm_error(module_name, "\n\tAVMM Interface: READ and WRITE requests cannot be sent simultaneously.");
    end

    assert property (ready_undefined)
    else begin
        `uvm_error(module_name, "\n\tAVMM Interface: READY must be always valid if RESET is not set.");
    end

    assert property (readdatavalid_undefined)
    else begin
        `uvm_error(module_name, "\n\tAVMM Interface: READDATAVALID must be always valid if RESET is not set.");
    end

endmodule

`endif
