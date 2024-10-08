/*
 * file       : driver.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: General MII UVM driver
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef MII_DRIVER_SV
`define MII_DRIVER_SV

class driver_rx #(int unsigned CHANNELS, int unsigned WIDTH) extends uvm_driver #(sequence_item #(CHANNELS, WIDTH));

    // ------------------------------------------------------------------------
    // Register component to database
    `uvm_component_param_utils(uvm_mii::driver_rx #(CHANNELS, WIDTH))

    localparam TOTAL_WIDTH = CHANNELS * WIDTH;
    localparam TOTAL_BYTES = CHANNELS * (WIDTH >> 3);

    // ------------------------------------------------------------------------
    // Virtual interface of rx driver
    virtual mii_if #(CHANNELS, WIDTH).driver_rx vif;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);

        WHOLE_BYTES : assert((WIDTH & 7) == 0);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.try_next_item(req);

            if (req != null) begin
                vif.driver_rx_cb.DATA      <= {>>1{req.data}};
                vif.driver_rx_cb.CONTROL   <= {>>1{req.control}};
                vif.driver_rx_cb.CLK_EN    <= req.clk_en;
                seq_item_port.item_done();
            end else begin
                vif.driver_rx_cb.DATA    <= {>>1{{TOTAL_WIDTH{1'bX}}}};
                vif.driver_rx_cb.CONTROL <= {>>1{{TOTAL_BYTES{1'bX}}}};
                vif.driver_rx_cb.CLK_EN  <= 1'bX;
            end
            @(vif.driver_rx_cb);
        end
    endtask

endclass

class driver_tx #(int unsigned CHANNELS, int unsigned WIDTH) extends uvm_driver #(sequence_item #(CHANNELS, WIDTH));

    // ------------------------------------------------------------------------
    // Register component to database
    `uvm_component_param_utils(uvm_mii::driver_tx #(CHANNELS, WIDTH))

    localparam TOTAL_WIDTH = CHANNELS * WIDTH;
    localparam TOTAL_BYTES = CHANNELS * (WIDTH >> 3);

    // ------------------------------------------------------------------------
    // Virtual interface of rx driver
    virtual mii_if #(CHANNELS, WIDTH).driver vif;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);

        WHOLE_BYTES : assert((WIDTH & 7) == 0);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.try_next_item(req);
            if (req != null) begin
                vif.driver_tx_cb.CLK_EN    <= req.clk_en;
                seq_item_port.item_done();
            end else begin
                vif.driver_tx_cb.CLK_EN  <= 1'bX;
            end
            @(vif.driver_tx_cb);
        end
    endtask

endclass

`endif
