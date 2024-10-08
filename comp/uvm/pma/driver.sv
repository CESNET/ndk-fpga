/*
 * file       : driver.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: PMA driver
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef PMA_DRIVER
`define PMA_DRIVER

// Driver of PMA interface
class driver #(int unsigned DATA_WIDTH) extends uvm_driver #(sequence_item #(DATA_WIDTH));

    // Register component to database.
    `uvm_component_param_utils(uvm_pma::driver #(DATA_WIDTH))

    // Virtual interface of driver
    virtual pma_if #(DATA_WIDTH).driver_cb vif;

    // Contructor of driver which contains name and parent component.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    task drive ();
        forever begin
            // Pull sequence item (transaction) from the low level sequencer.
            seq_item_port.try_next_item(req);
            if (req != null) begin
                vif.driver_cb.DATA       <= req.data;
                vif.driver_cb.HDR        <= req.hdr;
                vif.driver_cb.DATA_VLD   <= req.data_vld;
                vif.driver_cb.HDR_VLD    <= req.hdr_vld;
                vif.driver_cb.BLOCK_LOCK <= req.block_lock;
                seq_item_port.item_done();
                @(vif.driver_cb);
            end else begin
                vif.driver_cb.DATA_VLD       <= 1'b0;
                @(vif.driver_cb);
            end
        end
    endtask

    // Run - starts the processing in driver
    task run_phase(uvm_phase phase);
        drive();
    endtask

endclass

`endif
