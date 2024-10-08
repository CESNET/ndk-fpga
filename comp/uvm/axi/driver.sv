//-- driver.sv: AXI driver
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Driver of AXI rx interface
class driver_rx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS) extends uvm_driver #(sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS));

    // ------------------------------------------------------------------------
    // Register component to database
    `uvm_component_param_utils(uvm_axi::driver_rx #(DATA_WIDTH, TUSER_WIDTH, REGIONS))

    // ------------------------------------------------------------------------
    // Virtual interface of rx driver
    virtual axi_if #(DATA_WIDTH, TUSER_WIDTH).driver_rx vif;
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        rsp = sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("axi_rsp");

        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            if (req != null) begin
                // vif.driver_rx_cb.TDATA  <= req.tdata;
                for (int i = 0; i < REGIONS; i++) begin
                    vif.driver_rx_cb.TDATA[(i+1)*(DATA_WIDTH/REGIONS) - 1 -: (DATA_WIDTH/REGIONS)] <= req.tdata[i];
                end
                vif.driver_rx_cb.TUSER  <= req.tuser;
                vif.driver_rx_cb.TLAST  <= req.tlast;
                vif.driver_rx_cb.TKEEP  <= req.tkeep;
                vif.driver_rx_cb.TVALID <= req.tvalid;
                rsp.copy(req);
                rsp.set_id_info(req);
                seq_item_port.item_done();
            end else begin
                vif.driver_rx_cb.TDATA  <= 'X;
                vif.driver_rx_cb.TUSER  <= 'X;
                vif.driver_rx_cb.TLAST  <= 'X;
                vif.driver_rx_cb.TKEEP  <= 'X;
                vif.driver_rx_cb.TVALID <= 1'b0;
            end

            // Wait for the clocking block to write values to the registres
            @(vif.driver_rx_cb);

            if (req != null) begin
                rsp.tready = vif.driver_rx_cb.TREADY;
                seq_item_port.put_response(rsp);
            end
        end
    endtask

endclass

// Driver of AXI tx interface
class driver_tx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS) extends uvm_driver #(sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS));
    `uvm_component_param_utils(uvm_axi::driver_tx #(DATA_WIDTH, TUSER_WIDTH, REGIONS))

    // ------------------------------------------------------------------------
    // Virtual interface of driver
    virtual axi_if #(DATA_WIDTH, TUSER_WIDTH).driver_tx vif;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        req = uvm_axi::sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("mfb_rsp");

        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            // Assign values from requested sequence item to the interface
            if (req != null) begin
                vif.driver_tx_cb.TREADY <= req.tready;
                seq_item_port.item_done();
            end else begin
                vif.driver_tx_cb.TREADY <= 1'b0;
            end

            // Wait for the clocking block to write values to the registres
            @(vif.driver_tx_cb);

            if (req != null) begin
                seq_item_port.put_response(req);
            end
        end
    endtask
endclass
