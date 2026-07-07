// fce.sv: convert function avalon to pcie
// Copyright (C) 2025 CESNET z. s. p. o.
// Author:  Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


typedef enum {AVST_UP, AVST_DOWN} direction_t;

// hdr and prefix byte order as in INTEL P-TILE.
// 128-1:96 -> DWORD 0
//  96-1:64 -> DWORD 1
//  64-1:32 -> DWORD 2
//  32-1: 0 -> DWORD 3

function automatic void hdr_set(
    input uvm_pcie::header pcie_tr,
    output logic [128-1:0] hdr,
    output logic [32-1:0] prefix,
    output logic [1-1:0]  error,
    output logic [3-1:0]  bar,
    output logic [32-1:0] data[],
    input uvm_pcie::bar_config bar_cfg = null
);

    logic [3-1:0] fmt;
    logic [5-1:0] pcie_type;
    logic [1-1:0] r0;
    logic [3-1:0] tc;
    logic [1-1:0] r1;
    logic [3-1:0] attr;
    logic [1-1:0] r2;
    logic [1-1:0] th;
    logic [1-1:0] td;
    logic [1-1:0] ep;
    logic [2-1:0] at;
    logic [10-1:0] length;

    fmt       = pcie_tr.fmt;
    pcie_type = pcie_tr.pcie_type;
    r0        = 0;
    tc        = pcie_tr.traffic_class;
    r1        = 0;
    attr      = {pcie_tr.id_based_ordering, pcie_tr.relaxed_ordering, pcie_tr.no_snoop};
    r2        = 0;
    th        = pcie_tr.th;
    td        = pcie_tr.td;
    ep        = pcie_tr.ep;
    at        = pcie_tr.at;
    length    = pcie_tr.length;
    hdr[128-1:96] = {fmt, pcie_type, r0, tc, r1, attr[2], r2, th, td, ep, attr[2-1:0], at, length};

    // COMPLETER
    if (pcie_tr.hdr_type == uvm_pcie::header::COMPLETER_HDR) begin
        logic [16-1:0] completer_id;
        logic [3-1:0]  compl_status;
        logic [1-1:0]  bcm;
        logic [12-1:0] byte_count;
        logic [16-1:0] requester_id;
        logic [8-1:0]  tag;
        logic [1-1:0]  r0;
        logic [7-1:0]  lower_address;
        uvm_pcie::completer_header pcie_rc;

        $cast(pcie_rc, pcie_tr);

        completer_id = pcie_rc.completer_id;
        compl_status = pcie_rc.compl_status;
        bcm          = pcie_rc.bcm;
        byte_count   = pcie_rc.byte_count;
        requester_id = pcie_rc.requester_id;
        tag          = pcie_rc.tag;
        r0           = 0;
        lower_address  = pcie_rc.lower_address;
        hdr[32-1:0] = 'x;
        hdr[96-1:32] = {completer_id, compl_status, bcm, byte_count, requester_id, tag, r0, lower_address};
    // REQUEST
    end else if (pcie_tr.hdr_type == uvm_pcie::header::RQ_HDR) begin
        logic [16-1:0] requester_id;
        logic [8-1:0]  tag;
        logic [4-1:0]  lbe;
        logic [4-1:0]  fbe;
        logic [64-1:2] address;
        logic [2-1:0]  ph;
        uvm_pcie::request_header pcie_cq;

        $cast(pcie_cq, pcie_tr);

        requester_id = pcie_cq.requester_id;
        tag          = pcie_cq.tag;
        lbe          = pcie_cq.lbe;
        fbe          = pcie_cq.fbe;
        ph           = pcie_cq.ph;
        if (bar_cfg != null && pcie_cq.fmt[0] == 1'b0) begin
            address = pcie_cq.address[64-1:2];
            bar_cfg.addr2bar(bar, address);
        end else begin
            address  = pcie_cq.address[64-1:2];
            bar  =  0;
        end

        if (fmt[0] == 1'b0) begin
            hdr[32-1:0]     = 'x;
            hdr[96-1:32] = {requester_id, tag, lbe, fbe, address[32-1:2], ph};
        end else begin
            hdr[96-1:0]  = {requester_id, tag, lbe, fbe, address, ph};
        end
    end

    error = pcie_tr.ep;
    data  = pcie_tr.data;

    prefix = 0;
endfunction

// hdr and prefix byte order as in INTEL P-TILE.
// 128-1:96 -> DWORD 0
//  96-1:64 -> DWORD 1
//  64-1:32 -> DWORD 2
//  32-1: 0 -> DWORD 3

function automatic uvm_pcie::header hdr_get(
    input logic [128-1:0] hdr,
    input logic [32-1:0] prefix,
    input logic [1-1:0]  error,
    input logic [3-1:0]  bar,
    input logic [32-1:0] data[],
    input uvm_pcie::bar_config bar_cfg = null,
    input uvm_component parent = null
);
    uvm_pcie::header ret;
    const int unsigned REGION_SIZE = 8;

    logic [3-1:0] fmt;
    logic [5-1:0] pcie_type;
    logic [1-1:0] r0;
    logic [3-1:0] tc;
    logic [1-1:0] r1;
    logic [3-1:0] attr;
    logic [1-1:0] r2;
    logic [1-1:0] th;
    logic [1-1:0] td;
    logic [1-1:0] ep;
    logic [2-1:0] at;
    logic [10-1:0] length;

    {fmt, pcie_type, r0, tc, r1, attr[2], r2, th, td, ep, attr[2-1:0], at, length} = hdr[128-1:96];

    //Completer
    if ({fmt, pcie_type} == 8'b01001010) begin
        uvm_pcie::completer_header pcie_tr;
        logic [16-1:0] completer_id;
        logic [3-1:0]  compl_status;
        logic [1-1:0]  bcm;
        logic [12-1:0] byte_count;
        logic [16-1:0] requester_id;
        logic [8-1:0]  tag;
        logic [1-1:0]  r0;
        logic [7-1:0]  lower_address;

        {completer_id, compl_status, bcm, byte_count, requester_id, tag, r0, lower_address} = hdr[96-1:32];

        pcie_tr = uvm_pcie::completer_header::type_id::create("pcie_tr", parent);

        pcie_tr.fmt               = fmt;
        pcie_tr.pcie_type         = pcie_type;
        pcie_tr.traffic_class     = tc;
        pcie_tr.id_based_ordering = attr[2];
        pcie_tr.relaxed_ordering  = attr[1];
        pcie_tr.no_snoop          = attr[0];
        pcie_tr.th                = th;
        pcie_tr.td                = td;
        pcie_tr.ep                = ep | error;
        pcie_tr.at                = at;
        pcie_tr.length            = length;
        pcie_tr.completer_id      = completer_id;
        pcie_tr.compl_status      = compl_status;
        pcie_tr.bcm               = bcm;
        pcie_tr.byte_count        = byte_count;
        pcie_tr.requester_id      = requester_id;
        pcie_tr.tag               = tag;
        pcie_tr.lower_address     = lower_address;


        ret = pcie_tr;
    // REQUEST
    end else begin
        uvm_pcie::request_header pcie_tr;
        logic [16-1:0] requester_id;
        logic [8-1:0]  tag;
        logic [4-1:0]  lbe;
        logic [4-1:0]  fbe;
        logic [64-1:2] address;
        logic [2-1:0]  ph;

        if (fmt[0] == 1'b0) begin
            address[64-1:32] = 0;
            {requester_id, tag, lbe, fbe, address[32-1:2], ph} = hdr[96-1:32];
        end else begin
            {requester_id, tag, lbe, fbe, address, ph} = hdr[96-1:0];
        end

        if (bar_cfg != null && fmt[0] == 1'b0) begin
            bar_cfg.bar2addr(bar, address);
        end

        pcie_tr = uvm_pcie::request_header::type_id::create("pcie_tr", parent);
        pcie_tr.fmt               = fmt;
        pcie_tr.pcie_type         = pcie_type;
        pcie_tr.traffic_class     = tc;
        pcie_tr.id_based_ordering = attr[2];
        pcie_tr.relaxed_ordering  = attr[1];
        pcie_tr.no_snoop          = attr[0];
        pcie_tr.th                = th;
        pcie_tr.td                = td;
        pcie_tr.ep                = ep | error;
        pcie_tr.at                = at;
        pcie_tr.length            = length;
        pcie_tr.requester_id      = requester_id;
        pcie_tr.tag               = tag;
        pcie_tr.lbe               = lbe;
        pcie_tr.fbe               = fbe;
        pcie_tr.address           = address;
        pcie_tr.ph                = ph;

        ret = pcie_tr;
    end

    if (fmt[3-1:1] == 2'b01) begin
        const int unsigned length = ret.length != 0 ? ret.length : 1024;

        ret.data = new[length](data);
        assert (length <= data.size() && data.size() <= length + REGION_SIZE) else begin
            const
            string
            msg = $sformatf(
                "\n\tData length is not in required boundaries %0d <= %0d <= %0d\n%s",
                length,
                data.size(),
                length + REGION_SIZE,
                ret.convert2string()
            );
            `uvm_fatal(parent != null ? parent.get_full_name() : "", msg);
        end
    end

    return ret;
endfunction

