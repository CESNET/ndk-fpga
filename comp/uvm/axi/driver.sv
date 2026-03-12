//-- driver.sv: AXI driver
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Driver of AXI rx interface
class driver_rx #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_driver #(sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH));

    // ------------------------------------------------------------------------
    // Register component to database
    `ndk_component_param_utils(
        uvm_axi::driver_rx#(ITEMS, ITEM_WIDTH, TUSER_WIDTH),
        $sformatf("uvm_axi::driver_rx#(%0d,%0d,%0d)",ITEMS, ITEM_WIDTH, TUSER_WIDTH)
    )

    // ------------------------------------------------------------------------
    // Virtual interface of rx driver
    virtual axi_if #(ITEMS, ITEM_WIDTH, TUSER_WIDTH).driver_rx vif;
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            if (req != null) begin
                // vif.driver_rx_cb.TDATA  <= req.tdata;
                vif.driver_rx_cb.TDATA  <= req.tdata;
                vif.driver_rx_cb.TUSER  <= req.tuser;
                vif.driver_rx_cb.TLAST  <= req.tlast;
                vif.driver_rx_cb.TKEEP  <= req.tkeep;
                vif.driver_rx_cb.TVALID <= req.tvalid;

                // Wait for the clocking block to write values to the registres
                @(vif.driver_rx_cb);

                req.tready = vif.driver_rx_cb.TREADY;
                seq_item_port.item_done(req);
            end else begin
                vif.driver_rx_cb.TDATA  <= 'X;
                vif.driver_rx_cb.TUSER  <= 'X;
                vif.driver_rx_cb.TLAST  <= 'X;
                vif.driver_rx_cb.TKEEP  <= 'X;
                vif.driver_rx_cb.TVALID <= 1'b0;

                // Wait for the clocking block to write values to the registres
                @(vif.driver_rx_cb);
            end
        end
    endtask

endclass

// Driver of AXI tx interface
class driver_tx #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_driver #(sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH));
    `ndk_component_param_utils(
        uvm_axi::driver_tx#(ITEMS, ITEM_WIDTH, TUSER_WIDTH),
        $sformatf("uvm_axi::driver_tx#(%0d,%0d,%0d)",ITEMS, ITEM_WIDTH, TUSER_WIDTH)
    )

    // ------------------------------------------------------------------------
    // Virtual interface of driver
    virtual axi_if #(ITEMS, ITEM_WIDTH, TUSER_WIDTH).driver_tx vif;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            // Assign values from requested sequence item to the interface
            if (req != null) begin

                vif.driver_tx_cb.TREADY <= req.tready;

                // Wait for the clocking block to write values to the registres
                @(vif.driver_tx_cb);

                req.tdata  = vif.driver_tx_cb.TDATA;
                req.tuser  = vif.driver_tx_cb.TUSER;
                req.tlast  = vif.driver_tx_cb.TLAST;
                req.tkeep  = vif.driver_tx_cb.TKEEP;
                req.tvalid = vif.driver_tx_cb.TVALID;
                seq_item_port.item_done(req);
            end else begin
                vif.driver_tx_cb.TREADY <= 1'b0;

                // Wait for the clocking block to write values to the registres
                @(vif.driver_tx_cb);
            end

        end
    endtask
endclass
