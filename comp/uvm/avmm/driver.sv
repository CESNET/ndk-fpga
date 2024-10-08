// driver.sv: AVMM driver
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Slave
class driver_slave #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_driver #(sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH), sequence_item_response #(DATA_WIDTH));
    `uvm_component_param_utils(uvm_avmm::driver_slave #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // Virtual interface of slave driver
    virtual avmm_if #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH).driver_rx vif;

    // Response queue
    sequence_item_response #(DATA_WIDTH) responses[$];

    // Constructor
    function new(string name = "driver_slave", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Start driving signals to interface
    task run_phase(uvm_phase phase);
        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            if (req != null) begin
                vif.driver_slave_cb.READ       <= req.read;
                vif.driver_slave_cb.WRITE      <= req.write;
                vif.driver_slave_cb.ADDRESS    <= req.address;
                vif.driver_slave_cb.WRITEDATA  <= req.writedata;
                vif.driver_slave_cb.BURSTCOUNT <= req.burstcount;
            end
            else begin
                vif.driver_slave_cb.READ       <= '0;
                vif.driver_slave_cb.WRITE      <= '0;
                vif.driver_slave_cb.ADDRESS    <= 'X;
                vif.driver_slave_cb.WRITEDATA  <= 'X;
                vif.driver_slave_cb.BURSTCOUNT <= 'X;
            end

            // Wait for the clocking block to write values to the registers
            @(vif.driver_slave_cb);

            if (req != null) begin
                req.ready = vif.driver_slave_cb.READY;
                seq_item_port.item_done();

                if (req.ready === 1'b1 && req.read === 1'b1) begin
                    sequence_item_response #(DATA_WIDTH) response;
                    response = sequence_item_response #(DATA_WIDTH)::type_id::create("response");
                    response.set_id_info(req);
                    responses.push_back(response);
                end
            end

            // Return response
            if (vif.driver_slave_cb.READDATAVALID === 1'b1 && responses.size() != 0) begin
                sequence_item_response #(DATA_WIDTH) response;
                response = responses.pop_front();
                response.readdata      = vif.driver_slave_cb.READDATA;
                response.readdatavalid = vif.driver_slave_cb.READDATAVALID;
                seq_item_port.put(response);
            end
        end
    endtask

endclass

// Master
class driver_master #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_driver #(sequence_item_response #(DATA_WIDTH), sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH));
    `uvm_component_param_utils(uvm_avmm::driver_master #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // Virtual interface of master driver
    virtual avmm_if #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH).tb_master vif;

    // Constructor
    function new(string name = "driver_master", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Start driving signals to interface
    task run_phase(uvm_phase phase);
        forever begin
            // Get new sequence item to drive to interface
            seq_item_port.try_next_item(req);

            if (req != null) begin
                vif.driver_master_cb.READY         <= req.ready;
                vif.driver_master_cb.READDATA      <= req.readdata;
                vif.driver_master_cb.READDATAVALID <= req.readdatavalid;
            end
            else begin
                vif.driver_master_cb.READY         <= '0;
                vif.driver_master_cb.READDATA      <= 'X;
                vif.driver_master_cb.READDATAVALID <= '0;
            end

            // Wait for the clocking block to write values to the registers
            @(vif.driver_master_cb);

            if (req != null) begin
                rsp = sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("rsp");
                rsp.read       = vif.driver_master_cb.READ;
                rsp.write      = vif.driver_master_cb.WRITE;
                rsp.address    = vif.driver_master_cb.ADDRESS;
                rsp.writedata  = vif.driver_master_cb.WRITEDATA;
                rsp.burstcount = vif.driver_master_cb.BURSTCOUNT;
                rsp.ready      = req.ready;
                rsp.set_id_info(req);
                seq_item_port.item_done();
            end
        end
    endtask

endclass
