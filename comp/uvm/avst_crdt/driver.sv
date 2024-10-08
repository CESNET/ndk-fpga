// driver.sv: AVST credit control driver
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// ======= //
// RX side //
// ======= //

class driver_rx #(int unsigned UPDATE_CNT_WIDTH) extends uvm_driver #(sequence_item #(UPDATE_CNT_WIDTH));
    `uvm_component_param_utils(uvm_avst_crdt::driver_rx #(UPDATE_CNT_WIDTH))

    // Virtual interface
    virtual avst_crdt_if #(UPDATE_CNT_WIDTH).driver_rx vif;

    // Constructor
    function new(string name = "driver_rx", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Driving signals to interface
    task run_phase(uvm_phase phase);
        rsp = sequence_item #(UPDATE_CNT_WIDTH)::type_id::create("rsp");

        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            if (req != null) begin
                vif.driver_rx_cb.INIT       <= req.init;
                vif.driver_rx_cb.UPDATE     <= req.update;
                vif.driver_rx_cb.UPDATE_CNT <= req.update_cnt;
                seq_item_port.item_done();
            end else begin
                vif.driver_rx_cb.INIT       <= 1'b0;
                vif.driver_rx_cb.UPDATE     <= 1'b0;
                vif.driver_rx_cb.UPDATE_CNT <= 1'bX;
            end

            // Wait for the clocking block to write values
            @(vif.driver_rx_cb);

            if (req != null) begin
                // Set response data
                rsp.copy(req);
                rsp.init_ack = vif.driver_rx_cb.INIT_ACK;

                rsp.set_id_info(req);
                seq_item_port.put_response(rsp);
            end
        end
    endtask

endclass

// ======= //
// TX side //
// ======= //

class driver_tx #(int unsigned UPDATE_CNT_WIDTH) extends uvm_driver #(sequence_item #(UPDATE_CNT_WIDTH));
    `uvm_component_param_utils(uvm_avst_crdt::driver_tx #(UPDATE_CNT_WIDTH))

    // Virtual interface
    virtual avst_crdt_if #(UPDATE_CNT_WIDTH).driver_tx vif;

    // Constructor
    function new(string name = "driver_tx", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Start driving signals to interface
    task run_phase(uvm_phase phase);
        rsp = sequence_item #(UPDATE_CNT_WIDTH)::type_id::create("rsp");

        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            if (req != null) begin
                vif.driver_tx_cb.INIT_ACK <= req.init_ack;
                seq_item_port.item_done();
            end else begin
                vif.driver_tx_cb.INIT_ACK <= 1'b0;
            end

            // Wait for the clocking block to write values
            @(vif.driver_tx_cb);

            if (req != null) begin
                // Set response data
                rsp.copy(req);
                rsp.init       = vif.driver_tx_cb.INIT;
                rsp.update     = vif.driver_tx_cb.UPDATE;
                rsp.update_cnt = vif.driver_tx_cb.UPDATE_CNT;

                rsp.set_id_info(req);
                seq_item_port.put_response(rsp);
            end
        end
    endtask

endclass
