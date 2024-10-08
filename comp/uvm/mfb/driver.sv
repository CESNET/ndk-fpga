//-- driver.sv: Mfb driver
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Driver of mfb rx interface
class driver_rx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_driver #(sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH));

    // ------------------------------------------------------------------------
    // Register component to database
    `uvm_component_param_utils(uvm_mfb::driver_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    // ------------------------------------------------------------------------
    // Virtual interface of rx driver
    virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH).driver_rx vif;

    localparam SOF_POS_WIDTH = $clog2(REGION_SIZE);
    localparam EOF_POS_WIDTH = $clog2(REGION_SIZE * BLOCK_SIZE);
    localparam DATA_WIDTH    = REGION_SIZE * BLOCK_SIZE * ITEM_WIDTH;
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        rsp = sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("mfb_rsp");

        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            if (req != null) begin
                for (int i = 0; i < REGIONS; i++) begin
                    vif.driver_rx_cb.DATA[(i+1)*DATA_WIDTH - 1 -: DATA_WIDTH]         <= req.data[i];
                    if (META_WIDTH > 0) begin
                        vif.driver_rx_cb.META[(i+1)*META_WIDTH - 1 -: META_WIDTH]     <= req.meta[i];
                    end
                    if (SOF_POS_WIDTH > 0) begin
                        vif.driver_rx_cb.SOF_POS[(i+1)*SOF_POS_WIDTH -1 -: SOF_POS_WIDTH] <= req.sof_pos[i];
                    end
                    if (EOF_POS_WIDTH > 0) begin
                        vif.driver_rx_cb.EOF_POS[(i+1)*EOF_POS_WIDTH -1 -: EOF_POS_WIDTH] <= req.eof_pos[i];
                    end
                end
                vif.driver_rx_cb.SOF      <= req.sof;
                vif.driver_rx_cb.EOF      <= req.eof;
                vif.driver_rx_cb.SRC_RDY  <= req.src_rdy;
                rsp.copy(req);
                rsp.set_id_info(req);
                seq_item_port.item_done();
            end else begin
                vif.driver_rx_cb.DATA       <= 'X;
                vif.driver_rx_cb.META       <= 'X;
                vif.driver_rx_cb.SOF_POS    <= 'X;
                vif.driver_rx_cb.EOF_POS    <= 'X;
                vif.driver_rx_cb.SOF        <= 'X;
                vif.driver_rx_cb.EOF        <= 'X;
                vif.driver_rx_cb.SRC_RDY    <= 1'b0;
            end

            // Wait for the clocking block to write values to the registres
            @(vif.driver_rx_cb);

            if (req != null) begin
                rsp.dst_rdy = vif.driver_rx_cb.DST_RDY;
                seq_item_port.put_response(rsp);
            end
        end
    endtask

endclass

// Driver of mfb tx interface
class driver_tx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_driver #(sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH));
    `uvm_component_param_utils(uvm_mfb::driver_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    // ------------------------------------------------------------------------
    // Virtual interface of driver
    virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH).driver_tx vif;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        req = uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("mfb_rsp");;

        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            // Assign values from requested sequence item to the interface
            if (req != null) begin
                vif.driver_tx_cb.DST_RDY <= req.dst_rdy;
                seq_item_port.item_done();
            end else begin
                vif.driver_tx_cb.DST_RDY <= 1'b0;
            end

            // Wait for the clocking block to write values to the registres
            @(vif.driver_tx_cb);

            if (req != null) begin
                seq_item_port.put_response(req);
            end
        end
    endtask
endclass
