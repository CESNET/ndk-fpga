// fce.sv: convert function xilinx to pcie
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:  Radek Iša <isa@cesnet.cz> 

// SPDX-License-Identifier: BSD-3-Clause

//TODO: Add check when completed header countains error then data have to contain request headere
//TODO: ADD check when return error to xilinx ip core!! => there is bug (read xilinx documentation when returning not supported request)
//ret &= (5*4    === byte_count);
//ret &= (5      === dword_count);
//if ((tr_model.item.data.size() + 3) != tr_dut.in_item.data.size()) begin
//    return 0;
//end
function uvm_pcie::completer_header get_comp_hdr(uvm_logic_vector_array::sequence_item#(32) data, uvm_component comp = null);
    uvm_pcie::completer_header ret;
    logic [7-1:0] address;
    logic [1-1:0] r0;
    logic [2-1:0] at;
    logic [6-1:0] r1;
    logic [13-1:0] byte_count;
    logic [1-1:0] locked_read;
    logic [2-1:0] r2;
    logic [11-1:0] dword_count;
    logic [3-1:0] completion_status;
    logic [1-1:0] poisoned_completion;
    logic [1-1:0]  r3;
    logic [16-1:0] requester_id;
    logic [8-1:0] tag;
    logic [16-1:0] completer_id;
    logic [1-1:0] completer_id_en;
    logic [3-1:0] tc;
    logic [3-1:0] attr;
    logic [1-1:0] ecrc;

    ret = uvm_pcie::completer_header::type_id::create("ret", comp);
    {ecrc, attr, tc, completer_id_en, completer_id, tag, requester_id, r3,
    poisoned_completion, completion_status, dword_count, r2, locked_read,
    byte_count, r1, at, r0, address}
    = {data.data[2], data.data[1], data.data[0]};

    ret.fmt               = 3'b010;
    ret.pcie_type         = 5'b01010;
    ret.lower_address     = address;
    ret.at                = at;
    ret.th                = 0;
    ret.td                = 0;
    ret.ep                = poisoned_completion;
    ret.requester_id      = requester_id;
    ret.tag               = tag;
    ret.completer_id      = completer_id;
    ret.traffic_class     = tc;
    ret.id_based_ordering = attr[2];
    ret.relaxed_ordering  = attr[1];
    ret.no_snoop          = attr[0];
    ret.compl_status = completion_status;
    ret.bcm          = 0;
    ret.byte_count   = byte_count;
    ret.length       = dword_count;

    ret.data = new[data.data.size()-3];
    for (int unsigned it = 3; it < data.data.size(); it++) begin
        ret.data[it-3] = data.data[it];
    end

    return ret;
endfunction

function uvm_pcie::request_header get_rq_hdr(uvm_logic_vector_array::sequence_item#(32) data, uvm_component comp = null);
    uvm_pcie::request_header ret;
    logic [2-1:0]  at;
    logic [64-1:2] address;
    logic [11-1:0] length;
    logic [4-1:0]  req_type;
    logic [1-1:0]  poisoned_req;
    logic [16-1:0] requester_id;
    logic [8-1:0]  tag;
    logic [16-1:0] completer_id;
    logic [1-1:0]  requester_id_en;
    logic [3-1:0]  tc;
    logic [3-1:0]  attr;
    logic [1-1:0]  ecrc;

    {ecrc, attr, tc, requester_id_en, completer_id, tag, requester_id, poisoned_req, req_type, length,
    address, at}
    = {data.data[3], data.data[2], data.data[1], data.data[0]};

    ret = uvm_pcie::request_header::type_id::create("rq", comp);
    ret.at       = at;
    ret.address  = address;
    ret.length   = length;
    ret.fbe      = 4'b1111;
    ret.lbe      = (length != 1) ? 4'b1111 : 0;
    ret.fmt[0]   = (address[64-1:32] != 0);
    if (req_type === 4'b0000) begin
        ret.fmt[3-1:1] = 2'b00;
        ret.pcie_type  = 5'b00000;
    end else if (req_type === 4'b0001) begin
        ret.fmt[3-1:1] = 2'b01;
        ret.pcie_type  = 5'b00000;
    end else begin
        `uvm_fatal(comp != null ? comp.get_full_name() : "ROOT", "\n\tUnknow pcie transaction type");
    end

    ret.ph           = 0;
    ret.th           = 0;
    ret.td           = 0;
    ret.ep           = poisoned_req;
    ret.requester_id = requester_id;
    ret.tag          = tag;
    ret.traffic_class     = tc;
    ret.id_based_ordering = attr[2];
    ret.relaxed_ordering  = attr[1];
    ret.no_snoop          = attr[0];

    ret.data = new[data.data.size()-4];
    for (int unsigned it = 4; it < data.data.size(); it++) begin
       ret.data[it-4] = data.data[it];
    end
    return ret;
endfunction

