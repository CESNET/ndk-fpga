// sequence.sv: sequence
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class req_fifo#(type T_ITEM);
    protected T_ITEM items[$];

    function int unsigned size();
        return items.size();
    endfunction

    function void push_back(T_ITEM item);
        items.push_back(item);
    endfunction

    function T_ITEM pop_front();
        return items.pop_front();
    endfunction
endclass

class sequence_rc extends uvm_sequence #(uvm_logic_vector_array::sequence_item#(32));
    `uvm_object_param_utils(uvm_pcie_xilinx::sequence_rc)

    req_fifo#(uvm_pcie::completer_header) fifo; 

    // Constructor - creates new instance of this class
    function new(string name = "sequence_rc");
        super.new(name);
    endfunction

    task body();
        assert(uvm_config_db #(req_fifo#(uvm_pcie::completer_header))::get(m_sequencer, "", "seq_fifo_rc", fifo)) else begin
            `uvm_fatal(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get fifo rc"); 
        end;

        forever begin
            uvm_pcie::completer_header pcie_cc;
            int unsigned   length;
            logic [12-1:0] lower_addr;
            logic [4-1:0]  err_code;
            logic [13-1:0] byte_count;
            logic [1-1:0]  locked_read_completion;
            logic [1-1:0]  request_completed;
            logic [1-1:0]  r_0;
            logic [11-1:0] dword_count;
            logic [3-1:0]  completion_status;
            logic [1-1:0]  poisoned;
            logic [1-1:0]  r_1;
            logic [16-1:0] requester_id;
            logic [8-1:0]  tag;
            logic [16-1:0] completer_id;
            logic [1-1:0]  r_2;
            logic [3-1:0]  tc;
            logic [3-1:0]  attr;
            logic [1-1:0]  r_3;
            logic [32-1:0] hdr[3];
            int unsigned   move;

            //get header from 

            wait(fifo.size() != 0);
            pcie_cc = fifo.pop_front();

            req = uvm_logic_vector_array::sequence_item#(32)::type_id::create("req", m_sequencer);
            start_item(req);

            length = pcie_cc.length != 0 ? pcie_cc.length : 1024;

            lower_addr             = pcie_cc.lower_address;
            err_code               = 0;
            byte_count             = pcie_cc.byte_count;
            locked_read_completion = 0;
            move                   = pcie_cc.lower_address & 2'b11;
            request_completed      = (pcie_cc.byte_count <= (length*4 - move));
            r_0                    = 0;
            dword_count            = length;
            completion_status      = pcie_cc.compl_status;
            poisoned               = pcie_cc.ep;
            r_1                    = 0;
            requester_id           = pcie_cc.requester_id;
            tag                    = pcie_cc.tag;
            completer_id           = pcie_cc.completer_id;
            r_2                    = 0;
            tc                     = pcie_cc.traffic_class;
            attr[2]                = pcie_cc.id_based_ordering;
            attr[1]                = pcie_cc.relaxed_ordering;
            attr[0]                = pcie_cc.no_snoop;
            r_3                    = 0;

            {hdr[2], hdr[1], hdr[0]} = 
            {r_3, attr, tc, r_2, completer_id, tag, requester_id, r_1, poisoned, completion_status, dword_count, r_0, request_completed,
            locked_read_completion, byte_count, err_code, lower_addr};

            req.data = {hdr, pcie_cc.data};
            finish_item(req);
        end
    endtask
endclass

class sequence_cq extends uvm_sequence #(uvm_logic_vector_array::sequence_item#(32));
    `uvm_object_param_utils(uvm_pcie_xilinx::sequence_cq)

    req_fifo#(uvm_pcie::request_header) fifo; 

    // Constructor - creates new instance of this class
    function new(string name = "sequence_cq");
        super.new(name);
    endfunction

    task body();

        assert(uvm_config_db #(req_fifo#(uvm_pcie::request_header)  )::get(m_sequencer, "", "seq_fifo_cq", fifo)) else begin
            `uvm_fatal(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get fifo cq") 
        end;

        forever begin
            uvm_pcie::request_header pcie_cq;
            logic [2-1:0]  at;
            logic [64-1:2] address;
            logic [11-1:0] length;
            logic [4-1:0]  req_type;
            logic [16-1:0] requester_id;
            logic [8-1:0]  tag;
            logic [8-1:0]  target_function;
            logic [9-1:0]  bar;
            logic [3-1:0]  tc;
            logic [3-1:0]  attr;
            logic [1-1:0]  r0;
            logic [1-1:0]  r1;
            logic [32-1:0] hdr[4];

            wait(fifo.size() != 0);
            pcie_cq = fifo.pop_front();

            req = uvm_logic_vector_array::sequence_item#(32)::type_id::create("req", m_sequencer);
            start_item(req);

            case ({pcie_cq.fmt[3-1:1], pcie_cq.pcie_type})
                {2'b00, 5'b00000} : req_type = 4'b0000;
                {2'b01, 5'b00000} : req_type = 4'b0001;
                default : req_type = pcie_cq.pcie_type[4-1:0];
            endcase

            tc                =  pcie_cq.traffic_class;
            attr[2]           =  pcie_cq.id_based_ordering;
            attr[1]           =  pcie_cq.relaxed_ordering;
            attr[0]           =  pcie_cq.no_snoop;
            at                =  pcie_cq.at;
            length            =  pcie_cq.length != 0 ? pcie_cq.length : 1024;
            requester_id      =  pcie_cq.requester_id;
            tag               =  pcie_cq.tag;
            address           =  pcie_cq.address[64-1:2];
            bar[2:0]          =  0;
            bar[9-1:3]        =  26;
            target_function   =  0;
            //bar[2:0]          =  tr_out.item.bar;
            //bar[9-1:3]        =  tr_out.item.bar_aperture;
            //target_function   =  tr_out.item.vf;

            {hdr[3], hdr[2], hdr[1], hdr[0]} = {r1, attr, tc, bar, target_function, tag, requester_id, r0, req_type, length, address[64-1:2], at};
            req.data = {hdr, pcie_cq.data};
            finish_item(req);
        end
    endtask
endclass
