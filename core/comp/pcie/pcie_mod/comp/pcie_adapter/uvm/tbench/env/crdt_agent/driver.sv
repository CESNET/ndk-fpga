//-- driver.sv: AVST credit control driver
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

// Driver of AVST credit control rx interface
class driver_rx extends uvm_driver #(sequence_item);

    // ------------------------------------------------------------------------
    // Register component to database
    `uvm_component_param_utils(uvm_crdt::driver_rx)

    // ------------------------------------------------------------------------
    // Virtual interface of rx driver
    virtual crdt_if.driver_rx vif;

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
                vif.driver_rx_cb.INIT_DONE <= req.init_done;
                vif.driver_rx_cb.UPDATE    <= req.update;
                vif.driver_rx_cb.CNT_PH    <= req.cnt_ph;
                vif.driver_rx_cb.CNT_NPH   <= req.cnt_nph;
                vif.driver_rx_cb.CNT_CPLH  <= req.cnt_cplh;
                vif.driver_rx_cb.CNT_PD    <= req.cnt_pd;
                vif.driver_rx_cb.CNT_NPD   <= req.cnt_npd;
                vif.driver_rx_cb.CNT_CPLD  <= req.cnt_cpld;

                seq_item_port.item_done();
            end else begin
                vif.driver_rx_cb.INIT_DONE <= '0;
                vif.driver_rx_cb.UPDATE    <= 'X;
                vif.driver_rx_cb.CNT_PH    <= 'X;
                vif.driver_rx_cb.CNT_NPH   <= 'X;
                vif.driver_rx_cb.CNT_CPLH  <= 'X;
                vif.driver_rx_cb.CNT_PD    <= 'X;
                vif.driver_rx_cb.CNT_NPD   <= 'X;
                vif.driver_rx_cb.CNT_CPLD  <= 'X;
            end

            // Wait for the clocking block to write values to the registres
            @(vif.driver_rx_cb);
        end
    endtask

endclass

// Driver of AVST credit control tx interface
class driver_tx extends uvm_driver #(sequence_item);
    `uvm_component_param_utils(uvm_crdt::driver_tx)

    // ------------------------------------------------------------------------
    // Virtual interface of driver
    virtual crdt_if.driver_tx vif;

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
                vif.driver_tx_cb.INIT_DONE <= req.init_done;
                seq_item_port.item_done();
            end else begin
                vif.driver_tx_cb.INIT_DONE <= 1'b0;
            end

            // Wait for the clocking block to write values to the registres
            @(vif.driver_tx_cb);
        end
    endtask
endclass
