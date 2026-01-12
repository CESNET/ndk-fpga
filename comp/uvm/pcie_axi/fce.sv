// fce.sv: convert function xilinx to pcie
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:  Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

// TODO: Add check when completed header countains error then data have to contain request headere
// TODO: ADD check when return error to xilinx ip core!! => there is bug (read xilinx documentation when returning not supported request)
// TOOD: CORECT ALL HEADER: for RQ, CC, CQ, RC. Everyohne have different
// header.
// TOOD: CHECK ALL DEVICE (ULTRASCALE+, VERSAL) if they have same
// tuser width

typedef enum {AXI_RQ, AXI_RC, AXI_CQ, AXI_CC} direction_t;

//COUNT USER WIDTH
function automatic int unsigned tuser_width_get(int unsigned ITEMS, direction_t dir);
    automatic int unsigned ret = 0;

    if (ITEMS == 2 || ITEMS == 4 || ITEMS == 8) begin
        unique case (dir)
            AXI_RQ: ret = 85;
            AXI_RC: ret = 75;
            AXI_CQ: ret = 88;
            AXI_CC: ret = 33;
        endcase
    end else if (ITEMS == 16) begin
        unique case (dir)
            AXI_RQ: ret = 137;
            AXI_RC: ret = 161;
            AXI_CQ: ret = 183;
            AXI_CC: ret = 81;
        endcase
    end else begin
        $error("Unsupported number of items %0d\nSUPPORTED VALUES [2, 4, 8, 16]\n", ITEMS);
    end

    return ret;
endfunction


//////////////////////////////////////////////////////////////////////////////////////////////
// CC CONVERT
//////////////////////////////////////////////////////////////////////////////////////////////
function automatic uvm_pcie::completer_header hdr_cc_get(input logic[32-1:0] data[]);
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

    {ecrc, attr, tc, completer_id_en, completer_id, tag, requester_id, r3,
    poisoned_completion, completion_status, dword_count, r2, locked_read,
    byte_count, r1, at, r0, address}
    = {data[2], data[1], data[0]};

    ret = uvm_pcie::completer_header::type_id::create("cc_hdr");
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

    ret.data = new[data.size()-3];
    for (int unsigned it = 3; it < data.size(); it++) begin
        ret.data[it-3] = data[it];
    end
    return ret;
endfunction


function automatic void hdr_cc_set(output logic[32-1:0] data[3], input uvm_pcie::completer_header hdr);
    logic [13-1:0] byte_count;
    logic [1-1:0]  locked_read;
    logic [11-1:0] dword_count;
    logic [3-1:0]  attr;
    logic [1-1:0]  completer_id_en;
    logic [1-1:0]  ecrc;

    completer_id_en = 0;
    ecrc = 0;
    locked_read = 0;
    byte_count  = hdr.byte_count  != 0 ? hdr.byte_count  : 4096;
    dword_count = hdr.length      != 0 ? hdr.length : 1024;
    attr = {hdr.id_based_ordering, hdr.relaxed_ordering, hdr.no_snoop};

    {data[2], data[1], data[0]} =
    {ecrc, attr, hdr.traffic_class, completer_id_en, hdr.completer_id, hdr.tag, hdr.requester_id, 1'b0,
    hdr.ep, hdr.compl_status, dword_count, 2'b00, locked_read,
    byte_count, 6'b000000, hdr.at, 1'b0, hdr.lower_address};

endfunction


//////////////////////////////////////////////////////////////////////////////////////////////
// RC CONVERT
//////////////////////////////////////////////////////////////////////////////////////////////
function automatic uvm_pcie::completer_header hdr_rc_get(input logic[32-1:0] data[]);
    uvm_pcie::completer_header ret;
    logic [12-1:0] address;
    logic [4-1:0]  err_code;
    logic [13-1:0] byte_count;
    logic [1-1:0]  locked_read;
    logic [1-1:0]  request_compl;
    logic [1-1:0]  r0;
    logic [11-1:0] dword_count;
    logic [3-1:0] completion_status;
    logic [1-1:0] poisoned_completion;
    logic [1-1:0]  r1;
    logic [16-1:0] requester_id;
    logic [8-1:0] tag;
    logic [16-1:0] completer_id;
    logic [1-1:0] r2;
    logic [3-1:0] tc;
    logic [3-1:0] attr;
    logic [1-1:0] r3;

    {r3, attr, tc, r2, completer_id, tag, requester_id, r1,
    poisoned_completion, completion_status, dword_count, r0, request_compl, locked_read,
    byte_count, err_code, address}
    = {data[2], data[1], data[0]};

    ret = uvm_pcie::completer_header::type_id::create("rc_hdr");
    ret.fmt               = 3'b010;
    ret.pcie_type         = 5'b01010;
    ret.lower_address     = address;
    ret.at                = 0;
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

    ret.data = new[data.size()-3];
    for (int unsigned it = 3; it < data.size(); it++) begin
        ret.data[it-3] = data[it];
    end
    return ret;
endfunction


function automatic void hdr_rc_set(output logic[32-1:0] data[3], input uvm_pcie::completer_header hdr);
    logic [12-1:0] address;
    logic [4-1:0]  err_code;
    logic [13-1:0] byte_count;
    logic [1-1:0]  locked_read;
    logic [1-1:0]  request_compl;
    logic [11-1:0] dword_count;
    logic [3-1:0]  attr;
    int unsigned move;

    locked_read = 0;
    err_code    = 0;
    address     = hdr.lower_address;
    byte_count  = hdr.byte_count  != 0 ? hdr.byte_count  : 4096;
    dword_count = hdr.length      != 0 ? hdr.length : 1024;
    attr = {hdr.id_based_ordering, hdr.relaxed_ordering, hdr.no_snoop};
    move          = address & 2'b11;
    request_compl = (byte_count <= (dword_count*4 - move));

    {data[2], data[1], data[0]} =
    {1'b0, attr, hdr.traffic_class, 1'b0, hdr.completer_id, hdr.tag, hdr.requester_id, 1'b0,
    hdr.ep, hdr.compl_status, dword_count, 1'b0, request_compl, locked_read,
    byte_count, err_code, address};
endfunction



//////////////////////////////////////////////////////////////////////////////////////////////
// RQ CONVERT
//////////////////////////////////////////////////////////////////////////////////////////////
function automatic uvm_pcie::request_header hdr_rq_get(input logic[32-1:0] data[], input logic [4-1:0] fbe, input logic [4-1:0] lbe);
    uvm_pcie::request_header hdr;
    logic [2-1:0]  at;
    logic [64-1:2] address;
    logic [11-1:0] dword_count;
    logic [4-1:0]  req_type;
    logic [3-1:0]  attr;
    logic [3-1:0]  traffic_class;
    logic [8-1:0]  tag;
    logic [1-1:0]  requester_id_en;
    logic [16-1:0] requester_id;
    logic [16-1:0] completer_id;
    logic [1-1:0]  ep;
    logic [1-1:0]  ecrc; //reserved

    {ecrc, attr, traffic_class, requester_id_en, completer_id, tag, requester_id, ep, req_type, dword_count,
     address, at} =
    {data[3], data[2], data[1], data[0]};


    hdr = uvm_pcie::request_header::type_id::create("cq_hdr");

    hdr.address = address;
    hdr.fmt[0] = |hdr.address[64-1:32];
    if (req_type == 4'b0000) begin
        hdr.fmt[3-1:1] = 2'b00;
        hdr.pcie_type  = 5'b00000;
    end else if (req_type == 4'b0001) begin
        hdr.fmt[3-1:1] = 2'b01;
        hdr.pcie_type  = 5'b00000;
    end else begin
        `uvm_fatal("ROOT", $sformatf("\n\tUnknow pcie transaction type %b", req_type));
    end

    assert(requester_id_en == 0) else begin
         `uvm_fatal("ROOT", $sformatf("\n\tOnly support reqeust id enabled == 0 %b", requester_id_en));
    end
    hdr.ph           = 0;
    hdr.requester_id = requester_id;
    {hdr.id_based_ordering, hdr.relaxed_ordering, hdr.no_snoop} = attr;
    hdr.length = dword_count;
    hdr.tag = tag;
    hdr.traffic_class = traffic_class;
    hdr.th  = 0;
    hdr.td  = 0;
    hdr.ep  = ep;
    hdr.at  = at;
    hdr.fbe = fbe;
    hdr.lbe = lbe;

    hdr.data = new[data.size()-4];
    for (int unsigned it = 0; it < data.size()-4; it++) begin
        hdr.data[it] = data[it+4];
    end

    return hdr;
endfunction

function automatic void hdr_rq_set(output logic[32-1:0] data[4], input uvm_pcie::request_header hdr);
    logic [2-1:0]  at;
    logic [64-1:2] address;
    logic [11-1:0] dword_count;
    logic [4-1:0]  req_type;
    logic [3-1:0]  attr;
    logic [3-1:0]  traffic_class;
    logic [8-1:0]  tag;
    logic [1-1:0]  requester_id_en;
    logic [16-1:0] requester_id;
    logic [16-1:0] completer_id;
    logic [1-1:0]  ep;

    at      = hdr.at;
    address = hdr.address;
    requester_id_en = 0;
    requester_id = hdr.requester_id;
    completer_id = 0;
    dword_count = hdr.length != 0 ? hdr.length : 1024;
    if (hdr.fmt[3-1:1] == 2'b00 && hdr.pcie_type == 5'b00000) begin
        req_type = 4'b0000;
    end else if (hdr.fmt[3-1:1] == 2'b01 && hdr.pcie_type == 5'b00000) begin
        req_type = 4'b0001;
    end else begin
        `uvm_fatal("ROOT", "\n\tUnknow pcie transaction type");
    end
    attr = {hdr.id_based_ordering, hdr.relaxed_ordering, hdr.no_snoop};
    ep  = hdr.ep;
    tag = hdr.tag;
    traffic_class = hdr.traffic_class;

    {data[3], data[2], data[1], data[0]} =
    {1'b0, attr, traffic_class, requester_id_en, completer_id, tag, requester_id, ep, req_type, dword_count, address, at};
endfunction

//////////////////////////////////////////////////////////////////////////////////////////////
// CQ CONVERT
//////////////////////////////////////////////////////////////////////////////////////////////
function automatic uvm_pcie::request_header hdr_cq_get(input logic[32-1:0] data[], input logic [4-1:0] fbe, input logic [4-1:0] lbe, uvm_pcie::bar_config bar_cfg);
    uvm_pcie::request_header hdr;
    logic [11-1:0] dword_count;
    logic [4-1:0]  req_type;
    logic [3-1:0]  attr;
    logic [3-1:0]  bar;
    logic [64-1:2] address;
    logic [3-1:0]  traffic_class;
    logic [8-1:0]  tag;
    logic [16-1:0] requester_id;
    logic [2-1:0]  at;
    logic [6-1:0] bar_aperture;
    logic [8-1:0]  target_fce;
    logic [1-1:0]  r0; //reserved
    logic [1-1:0]  r1; //reserved

    {r0, attr, traffic_class, bar_aperture, bar, target_fce, tag, requester_id, r1, req_type, dword_count, address, at} =
    {data[3], data[2], data[1], data[0]};


    hdr = uvm_pcie::request_header::type_id::create("cq_hdr");

    if (bar_cfg != null && (|address[64-1:32]) == 1'b0) begin
        hdr.address = address;
        bar_cfg.bar2addr(bar, hdr.address);
    end else begin
        hdr.address = address;
    end

    hdr.fmt[0] = |hdr.address[64-1:32];
    if (req_type == 4'b0000) begin
        hdr.fmt[3-1:1] = 2'b00;
        hdr.pcie_type  = 5'b00000;
    end else if (req_type == 4'b0001) begin
        hdr.fmt[3-1:1] = 2'b01;
        hdr.pcie_type  = 5'b00000;
    end else begin
        `uvm_fatal("ROOT", "\n\tUnknow pcie transaction type");
    end

    hdr.ph           = 0;
    hdr.requester_id = requester_id;
    {hdr.id_based_ordering, hdr.relaxed_ordering, hdr.no_snoop} = attr;
    hdr.length = dword_count;
    hdr.tag = tag;
    hdr.traffic_class = traffic_class;
    hdr.th  = 0;
    hdr.td  = 0;
    hdr.ep  = 0;
    hdr.at  = at;
    hdr.fbe = fbe;
    hdr.lbe = lbe;

    hdr.data = new[data.size()-4];
    for (int unsigned it = 0; it < data.size()-4; it++) begin
        hdr.data[it] = data[it+4];
    end
    return hdr;
endfunction


function automatic void hdr_cq_set(output logic[32-1:0] data[4], input uvm_pcie::request_header hdr, logic [8-1:0]  target_fce, uvm_pcie::bar_config bar_cfg, logic [6-1:0] bar_aperture = 26);
    logic [11-1:0] dword_count;
    logic [4-1:0]  req_type;
    logic [3-1:0]  attr;
    logic [3-1:0]  bar;
    logic [64-1:2] address;

    attr = {hdr.id_based_ordering, hdr.relaxed_ordering, hdr.no_snoop};
    dword_count = hdr.length != 0 ? hdr.length : 1024;
    // TODO:
    if (hdr.fmt[3-1:1] == 2'b00 && hdr.pcie_type == 5'b00000) begin
        req_type = 4'b0000;
    end else if (hdr.fmt[3-1:1] == 2'b01 && hdr.pcie_type == 5'b00000) begin
        req_type = 4'b0001;
    end else begin
        `uvm_fatal("ROOT", "\n\tUnknow pcie transaction type");
    end

    if (bar_cfg != null && hdr.fmt[0] == 1'b0) begin
        address = hdr.address;
        bar_cfg.addr2bar(bar, address);
    end else begin
        address = hdr.address;
        bar     = 0;
    end

    {data[3], data[2], data[1], data[0]} =
    {1'b0, attr, hdr.traffic_class, bar_aperture, bar, target_fce, hdr.tag, hdr.requester_id, 1'b0, req_type, dword_count, address, hdr.at};
endfunction

