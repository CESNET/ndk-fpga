/*
 * file       : convertor to
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: convertor from uvm_mi::monitor to reg2bus predictor
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`uvm_analysis_imp_decl(_rq)
`uvm_analysis_imp_decl(_rs)

class reg2bus_class  extends uvm_sequence_item;
    `uvm_object_utils(reg2bus_class)

    uvm_reg_bus_op op;

    function new(string name = "reg2bus_class");
        super.new(name);
    endfunction

    function void do_copy(uvm_object rhs);
        reg2bus_class rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "mi::sequence_item_request::do_copy ", "Failed to cast transaction object.")
            return;
        end

        op = rhs_.op;
    endfunction
endclass

// Monitor convert bus transaction to reg transaction
class reg2bus_monitor #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_monitor;
    `uvm_component_param_utils(uvm_mi::reg2bus_monitor#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    reg2bus_class rq_que[$];
    // Reference to the virtual interface, initialized during the connect phase by parent agent.
    typedef reg2bus_monitor#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) this_type;
    uvm_analysis_imp_rq#(sequence_item_request#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH), this_type)  analysis_imp_rq;
    uvm_analysis_imp_rs#(sequence_item_response#(DATA_WIDTH), this_type)                          analysis_imp_rs;

    uvm_analysis_port #(reg2bus_class) analysis_port;


    function new (string name, uvm_component parent);
        super.new(name, parent);
        analysis_imp_rq     = new("analysis_imp_rq", this);
        analysis_imp_rs     = new("analysis_imp_rs", this);
        analysis_port = new("analysis_port", this);
    endfunction

    function void write_rq(sequence_item_request#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tr);
        if (tr.ardy == 1) begin
            reg2bus_class item = new();
            item.op.n_bits = DATA_WIDTH;
            if (tr.wr == 1) begin
                item.op.kind    = UVM_WRITE;
                item.op.byte_en = tr.be;
                item.op.data    = tr.dwr;
                item.op.addr    = tr.addr;
                item.op.status  = UVM_IS_OK;
                analysis_port.write(item);
            end

            if (tr.rd == 1) begin
                item.op.kind    = UVM_READ;
                item.op.byte_en = tr.be;
                item.op.data    = 'x;
                item.op.addr    = tr.addr;
                rq_que.push_back(item);
            end
        end
    endfunction


    function void write_rs(sequence_item_response#(DATA_WIDTH) tr);
        if (tr.drdy == 1 && rq_que.size() > 0) begin
            reg2bus_class item = rq_que.pop_front();

            item.op.data   = tr.drd;
            item.op.status = UVM_IS_OK;
            analysis_port.write(item);
        end
    endfunction
endclass

