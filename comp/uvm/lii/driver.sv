/*
 * file       : driver.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII driver
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef LII_DRIVER
`define LII_DRIVER

// Driver of LII interface
class driver_rx #(int unsigned DATA_WIDTH, logic FAST_SOF, int unsigned META_WIDTH, int unsigned SOF_WIDTH) extends uvm_driver #(sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH));

    // Register component to database.
    `uvm_component_param_utils(uvm_lii::driver_rx #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH))

    // Virtual interface of driver
    virtual lii_if #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH).driver_rx_cb vif;
    logic state = 1'b0;
    time time_of_fall;

    // Contructor of driver which contains name and parent component.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    task run_phase_fast_sof_down ();
            forever begin
               // Pull sequence item (transaction) from the low level sequencer.
                seq_item_port.try_next_item(req);
                if (req != null) begin
                    vif.driver_rx_cb.DATA        <= req.data;
                    vif.driver_rx_cb.BYTES_VLD   <= req.bytes_vld;
                    vif.driver_rx_cb.SOF         <= req.sof;
                    vif.driver_rx_cb.EOF         <= req.eof;
                    vif.driver_rx_cb.EEOF        <= req.eeof;
                    vif.driver_rx_cb.EDB         <= req.edb;
                    vif.driver_rx_cb.META        <= req.meta;
                    vif.driver_rx_cb.RXDECERR    <= req.rxdecerr;
                    vif.driver_rx_cb.RXSEQERR    <= req.rxseqerr;
                    vif.driver_rx_cb.LINK_STATUS <= req.link_status;

                    @(vif.driver_rx_cb);

                    rsp = sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)::type_id::create("rsp");
                    rsp.rdy = vif.driver_rx_cb.RDY;

                    rsp.set_id_info(req);

                    seq_item_port.item_done(rsp);
                    if (req.link_status == 1'b0) begin
                        #(125us);
                        @(vif.driver_rx_cb);
                    end
                end else begin
                    vif.driver_rx_cb.EOF <= 1'b0;
                    vif.driver_rx_cb.SOF <= 1'b0;
                    @(vif.driver_rx_cb);
                end
            end
    endtask

    // Run - starts the processing in driver
    task run_phase(uvm_phase phase);
        run_phase_fast_sof_down();
    endtask

endclass


// Driver of LII TX interface
class driver_tx #(int unsigned DATA_WIDTH, logic FAST_SOF, int unsigned META_WIDTH, int unsigned SOF_WIDTH) extends uvm_driver #(sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH));

    // ------------------------------------------------------------------------
    // Register component to database
    `uvm_component_param_utils(uvm_lii::driver_tx #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH))


    // ------------------------------------------------------------------------
    // Virtual interface of driver
    virtual lii_if #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH).driver_tx_cb vif;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        forever begin
            if (vif.driver_tx_cb.RESET != 1) begin
                // Get new sequence item to drive to interface
                seq_item_port.get_next_item(req);

                // Assign values from requested sequence item to the interface
                vif.driver_tx_cb.RDY <= req.rdy;

                // Wait for the clocking block to write values to the registres
                @(vif.driver_tx_cb);

                // Setup default data to the interface
                vif.driver_tx_cb.RDY <= 1'b0;

                seq_item_port.item_done();

            end else begin
                // Wait for the clocking block to write values to the registres
                @(vif.driver_tx_cb);
                // Setup default data to the interface
                vif.driver_tx_cb.RDY <= 1'b0;
            end

        end
    endtask

endclass

// Driver of LII ETH PHZ interface
class driver_rx_eth_phy #(int unsigned DATA_WIDTH, logic FAST_SOF, int unsigned META_WIDTH, logic MEAS, int unsigned SOF_WIDTH) extends uvm_driver #(sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH));

    // Register component to database.
    `uvm_component_param_utils(uvm_lii::driver_rx_eth_phy #(DATA_WIDTH, FAST_SOF, META_WIDTH, MEAS, SOF_WIDTH))

    // Virtual interface of driver
    virtual lii_if #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH).driver_rx_eth_phy_cb vif;

    // Contructor of driver which contains name and parent component.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    task run_phase_fast_sof_down ();
            forever begin
               // Pull sequence item (transaction) from the low level sequencer.
                seq_item_port.try_next_item(req);
                if (req != null) begin
                    if (vif.driver_rx_eth_phy_cb.LINK_STATUS == 1'b0 && MEAS == 1) begin
                        @(vif.driver_rx_eth_phy_cb.LINK_STATUS == 1'b1);
                    end
                    vif.driver_rx_eth_phy_cb.DATA        <= req.data;
                    vif.driver_rx_eth_phy_cb.BYTES_VLD   <= req.bytes_vld;
                    vif.driver_rx_eth_phy_cb.SOF         <= req.sof;
                    vif.driver_rx_eth_phy_cb.EOF         <= req.eof;
                    vif.driver_rx_eth_phy_cb.EEOF        <= req.eeof;
                    vif.driver_rx_eth_phy_cb.EDB         <= req.edb;
                    vif.driver_rx_eth_phy_cb.META        <= req.meta;
                    vif.driver_rx_eth_phy_cb.CRCERR      <= req.crcerr;

                    @(vif.driver_rx_eth_phy_cb);

                    rsp = sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)::type_id::create("rsp");
                    rsp.rdy = vif.driver_rx_eth_phy_cb.RDY;

                    rsp.set_id_info(req);

                    seq_item_port.item_done(rsp);
                end else begin
                    vif.driver_rx_eth_phy_cb.EOF <= 1'b0;
                    vif.driver_rx_eth_phy_cb.SOF <= 1'b0;
                    @(vif.driver_rx_eth_phy_cb);
                end
            end
    endtask

    // Run - starts the processing in driver
    task run_phase(uvm_phase phase);
        run_phase_fast_sof_down();
    endtask

endclass

`endif
