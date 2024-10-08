/*
 * file       : draiver.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: mi driver (slave master)
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class driver_slave #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_driver #(sequence_item_request #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH), sequence_item_response #(DATA_WIDTH));

    // Register component to database.
    `uvm_component_param_utils(uvm_mi::driver_slave #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    // Virtual interface of driver
    virtual mi_if #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH).tb_slave vif;
    //requests
    sequence_item_response #(DATA_WIDTH) res_que[$];

    // Contructor of driver which contains name and parent component.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Run - starts the processing in driver
    task run_phase(uvm_phase phase);
        forever begin
            // Pull sequence item (transaction) from the low level sequencer.
            seq_item_port.try_next_item(req);
            if (req != null) begin
                vif.cb_slave.ADDR  <= req.addr;
                vif.cb_slave.BE    <= req.be;
                vif.cb_slave.WR    <= req.wr;
                vif.cb_slave.DWR   <= req.dwr;
                vif.cb_slave.META   <= req.meta;
                vif.cb_slave.RD    <= req.rd;
            end else begin
                vif.cb_slave.ADDR  <= 'x;
                vif.cb_slave.BE    <= 'x;
                vif.cb_slave.WR    <= 1'b0;
                vif.cb_slave.DWR   <= 'x;
                vif.cb_slave.META   <= 'x;
                vif.cb_slave.RD    <= 1'b0;
            end

            @(vif.cb_slave);

            if (req != null) begin
                req.ardy = vif.cb_slave.ARDY;
                seq_item_port.item_done();
                if (req.rd == 1'b1 && req.ardy == 1'b1) begin
                    sequence_item_response #(DATA_WIDTH) res;
                    res = sequence_item_response #(DATA_WIDTH)::type_id::create();
                    res.set_id_info(req);
                    res_que.push_back(res);
                end
            end

            if (vif.cb_slave.DRDY === 1'b1 && res_que.size() != 0) begin
                sequence_item_response #(DATA_WIDTH) res;

                res = res_que.pop_front();
                res.drdy = vif.cb_slave.DRDY;
                res.ardy = vif.cb_slave.ARDY;
                res.drd  = vif.cb_slave.DRD;
                seq_item_port.put(res);
           end
        end
    endtask
endclass

class driver_master #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_driver #(sequence_item_response #(DATA_WIDTH), sequence_item_request #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH));
    // Register component to database.
    `uvm_component_param_utils(uvm_mi::driver_master#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    // Virtual interface of driver
    virtual mi_if #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH).tb_master vif;

    // Contructor of driver which contains name and parent component.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Run - starts the processing in driver
    task run_phase(uvm_phase phase);
        rsp = sequence_item_request #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("mi_master");
        forever begin
            // Pull sequence item (transaction) from the low level sequencer.
            seq_item_port.try_next_item(req);
            if (req != null) begin
                vif.cb_master.DRD  <= req.drd;
                vif.cb_master.ARDY <= req.ardy;
                vif.cb_master.DRDY <= req.drdy;
            end else begin
                vif.cb_master.DRD  <= 'x;
                vif.cb_master.ARDY <= 1'b0;
                vif.cb_master.DRDY <= 1'b0;
            end
            @(vif.cb_master);

            if (req != null) begin
                rsp.addr = vif.cb_master.ADDR;
                rsp.be   = vif.cb_master.BE;
                rsp.wr   = vif.cb_master.WR;
                rsp.dwr  = vif.cb_master.DWR;
                rsp.meta = vif.cb_master.META;
                rsp.rd   = vif.cb_master.RD;
                rsp.ardy = req.ardy;
                rsp.set_id_info(req);
                seq_item_port.item_done(rsp);
            end
        end
    endtask
endclass

