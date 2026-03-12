//-- driver.sv: AVST driver
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Driver of mfb rx interface
class driver_rx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_driver #(sequence_item #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH));

    // ------------------------------------------------------------------------
    // Register component to database
    `ndk_component_param_utils(
        uvm_avst::driver_rx#(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH),
        $sformatf("uvm_avst::driver_rx#(%0d,%0d,%0d,%0d)",REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH)
    )

    // ------------------------------------------------------------------------
    // Virtual interface of rx driver
    virtual avst_if #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH).driver_rx vif;

    localparam EMPTY_WIDTH = $clog2(REGION_SIZE);
    localparam DATA_WIDTH    = REGION_SIZE * ITEM_WIDTH;
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        rsp = sequence_item #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("mfb_rsp");

        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            if (req != null) begin
                vif.driver_rx_cb.DATA  <= req.data;
                vif.driver_rx_cb.META  <= req.meta;
                vif.driver_rx_cb.EMPTY <= req.empty;
                vif.driver_rx_cb.VALID <= req.valid;
                vif.driver_rx_cb.SOP <= req.sop;
                vif.driver_rx_cb.EOP <= req.eop;
                rsp.copy(req);
                rsp.set_id_info(req);
                seq_item_port.item_done();

                // Wait for the clocking block to write values to the registres
                @(vif.driver_rx_cb);

                rsp.ready = vif.driver_rx_cb.READY;
                seq_item_port.put_response(rsp);
            end else begin
                for (int unsigned it = 0; it < REGIONS; it++) begin
                    vif.driver_rx_cb.DATA[it]   <= 'X;
                    vif.driver_rx_cb.META[it]   <= 'X;
                    vif.driver_rx_cb.EMPTY[it]  <= 'X;
                end
                vif.driver_rx_cb.SOP    <= 'X;
                vif.driver_rx_cb.EOP    <= 'X;
                vif.driver_rx_cb.VALID  <= '0;

                // Wait for the clocking block to write values to the registres
                @(vif.driver_rx_cb);
            end
        end
    endtask

endclass

// Driver of mfb tx interface
class driver_tx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_driver #(sequence_item #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH));
    `ndk_component_param_utils(
        uvm_avst::driver_tx#(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH),
        $sformatf("uvm_avst::driver_tx#(%0d,%0d,%0d,%0d)",REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH)
    )

    // ------------------------------------------------------------------------
    // Virtual interface of driver
    virtual avst_if #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH).driver_tx vif;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        req = uvm_avst::sequence_item #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("mfb_rsp");;

        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            // Assign values from requested sequence item to the interface
            if (req != null) begin
                vif.driver_tx_cb.READY <= req.ready;
                seq_item_port.item_done();

                // Wait for the clocking block to write values to the registres
                @(vif.driver_tx_cb);

                seq_item_port.put_response(req);
            end else begin
                vif.driver_tx_cb.READY <= 1'b0;

                // Wait for the clocking block to write values to the registres
                @(vif.driver_tx_cb);
            end
        end
    endtask
endclass
