/*
 * file       : sequencer.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: driver for Intel mac seq interface
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class driver_rx #(int unsigned SEGMENTS) extends uvm_driver #(sequence_item #(SEGMENTS));
    `uvm_component_param_utils(uvm_intel_mac_seg::driver_rx #(SEGMENTS))

    // Virtual interface of rx driver
    virtual intel_mac_seg_if #(SEGMENTS).driver_rx vif;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.try_next_item(req);
            if (req != null) begin
                vif.driver_rx_cb.DATA        <= {<<64{req.data}};
                vif.driver_rx_cb.INFRAME     <= {<<1{req.inframe}};
                vif.driver_rx_cb.EOP_EMPTY   <= {<<3{req.eop_empty}};
                vif.driver_rx_cb.FCS_ERROR   <= {<<1{req.fcs_error}};
                vif.driver_rx_cb.ERROR       <= {<<2{req.error}};
                vif.driver_rx_cb.STATUS_DATA <= {<<3{req.status_data}};
                vif.driver_rx_cb.VALID       <= req.valid;
                seq_item_port.item_done();
            end else begin
                vif.driver_rx_cb.DATA        <= 'X;
                vif.driver_rx_cb.INFRAME     <= 0;
                vif.driver_rx_cb.EOP_EMPTY   <= 'X;
                vif.driver_rx_cb.FCS_ERROR   <= 'X;
                vif.driver_rx_cb.ERROR       <= 'X;
                vif.driver_rx_cb.STATUS_DATA <= 'X;
                vif.driver_rx_cb.VALID       <= '0;
            end

            @(vif.driver_rx_cb);

            if (req != null) begin
                req.ready = vif.driver_rx_cb.READY;
                seq_item_port.put_response(req);
                //seq_item_port.item_done(req);
            end
        end
    endtask
endclass


class driver_tx #(int unsigned SEGMENTS) extends uvm_driver #(sequence_item #(SEGMENTS));
    `uvm_component_param_utils(uvm_intel_mac_seg::driver_tx #(SEGMENTS))

    // Virtual interface of rx driver
    virtual intel_mac_seg_if #(SEGMENTS).driver_tx vif;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.try_next_item(req);
            if (req != null) begin
                vif.driver_tx_cb.READY <= req.ready;
            end else begin
                vif.driver_tx_cb.READY <= '0;
            end

            @(vif.driver_tx_cb);

            if (req != null) begin
                {<<64{req.data}}       =  vif.driver_tx_cb.DATA;
                {<<1{req.inframe}}     =  vif.driver_tx_cb.INFRAME;
                {<<3{req.eop_empty}}   =  vif.driver_tx_cb.EOP_EMPTY;
                {<<1{req.fcs_error}}   =  vif.driver_tx_cb.FCS_ERROR;
                {<<2{req.error}}       =  (2*SEGMENTS)'('h0);
                {<<3{req.status_data}} =  (3*SEGMENTS)'('h0);
                req.valid              =  vif.driver_tx_cb.VALID;
                seq_item_port.item_done(req);
            end
        end
    endtask
endclass

