// driver.sv: LBUS driver
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// ======= //
// TX side //
// ======= //

class driver_tx extends uvm_driver #(sequence_item);
    `uvm_component_utils(uvm_lbus::driver_tx)

    // Virtual interface
    virtual lbus_if.driver_tx vif;

    // Constructor
    function new(string name = "driver_tx", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Driving signals to interface
    task run_phase(uvm_phase phase);
        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            if (req != null) begin
                vif.driver_tx_cb.DATA <= req.data;
                vif.driver_tx_cb.ENA  <= req.ena;
                vif.driver_tx_cb.SOP  <= req.sop;
                vif.driver_tx_cb.EOP  <= req.eop;
                vif.driver_tx_cb.ERR  <= req.err;
                vif.driver_tx_cb.MTY  <= req.mty;
                // Start a request
                rsp = sequence_item::type_id::create("rsp");
                rsp.copy(req);
                rsp.set_id_info(req);
                // Complete request processing
                seq_item_port.item_done();
            end else begin
                vif.driver_tx_cb.DATA <= 'X;
                vif.driver_tx_cb.ENA  <= '0;
                vif.driver_tx_cb.SOP  <= 'X;
                vif.driver_tx_cb.EOP  <= 'X;
                vif.driver_tx_cb.ERR  <= 'X;
                vif.driver_tx_cb.MTY  <= 'X;
            end

            // Wait for the clocking block to write values
            @(vif.driver_tx_cb);

            if (req != null) begin
                // Set response data
                rsp.rdy = vif.driver_tx_cb.RDY;
                // Complete response processing
                seq_item_port.put_response(rsp);
            end
        end
    endtask

endclass

// ======= //
// RX side //
// ======= //

class driver_rx extends uvm_driver #(sequence_item);
    `uvm_component_utils(uvm_lbus::driver_rx)

    // Virtual interface
    virtual lbus_if.driver_rx vif;

    // Constructor
    function new(string name = "driver_rx", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Start driving signals to interface
    task run_phase(uvm_phase phase);
        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            if (req != null) begin
                vif.driver_rx_cb.RDY <= req.rdy;
                seq_item_port.item_done();
            end else begin
                vif.driver_rx_cb.RDY <= 1'b0;
            end

            // Wait for the clocking block to write values
            @(vif.driver_rx_cb);
        end
    endtask

endclass
