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

class sequence_data extends uvm_sequence #(uvm_logic_vector_array::sequence_item#(32));
    `uvm_object_param_utils(uvm_pcie_intel::sequence_data)

    req_fifo#(uvm_pcie::header) fifo;

    // Constructor - creates new instance of this class
    function new(string name = "sequence_rc");
        super.new(name);
    endfunction

    task body();
        assert(uvm_config_db #(req_fifo#(uvm_pcie::header))::get(m_sequencer, "", "seq_fifo", fifo)) else begin
            `uvm_fatal(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get fifo data"); 
        end;

        forever begin
            uvm_pcie::header pcie_tr;

            wait(fifo.size() != 0);
            pcie_tr = fifo.pop_front();

            req = uvm_logic_vector_array::sequence_item#(32)::type_id::create("req", m_sequencer);
            start_item(req);

            if (pcie_tr.data.size() != 0) begin
                req.data = new[pcie_tr.data.size()];
                for (int unsigned it = 0; it < pcie_tr.data.size(); it++) begin
                    req.data[it] = pcie_tr.data[it];
                end
            end else begin
                req.data = new[1];
                req.data[0] = 'x;
            end
            finish_item(req);
        end
    endtask
endclass

class sequence_meta#(META_WIDTH_DOWN) extends uvm_sequence #(uvm_logic_vector::sequence_item#(META_WIDTH_DOWN));
    `uvm_object_param_utils(uvm_pcie_intel::sequence_meta#(META_WIDTH_DOWN))


    localparam int unsigned HDR_WIDTH       = 128;
    localparam int unsigned PREFIX_WIDTH    = 32;
    localparam int unsigned BAR_RANGE_WIDTH = 3;


    req_fifo#(uvm_pcie::header) fifo; 

    // Constructor - creates new instance of this class
    function new(string name = "sequence_rc");
        super.new(name);
    endfunction

    task body();

        assert(uvm_config_db #(req_fifo#(uvm_pcie::header))::get(m_sequencer, "", "seq_fifo", fifo)) else begin
            `uvm_fatal(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get fifo data"); 
        end;

        forever begin
            logic [HDR_WIDTH-1:0]        hdr;
            logic [PREFIX_WIDTH-1:0]     prefix;
            logic [BAR_RANGE_WIDTH-1: 0] bar;
            logic [3-1:0] fmt;
            logic [5-1:0] pcie_type;
            logic [1-1:0] r0;
            logic [3-1:0] tc;
            logic [1-1:0] r1;
            logic [1-1:0] attr0;
            logic [1-1:0] r2;
            logic [1-1:0] th;
            logic [1-1:0] td;
            logic [1-1:0] ep;
            logic [2-1:0] attr1;
            logic [2-1:0] at;
            logic [10-1:0] length;
            uvm_pcie::header pcie_tr;

            wait(fifo.size() != 0);
            pcie_tr = fifo.pop_front();

            req = uvm_logic_vector::sequence_item#(META_WIDTH_DOWN)::type_id::create("req", m_sequencer);
            start_item(req);

            fmt       = pcie_tr.fmt;
            pcie_type = pcie_tr.pcie_type;
            r0        = 0;
            tc        = pcie_tr.traffic_class;
            r1        = 0;
            attr0     = pcie_tr.id_based_ordering;
            r2        = 0;
            th        = pcie_tr.th;
            td        = pcie_tr.td;
            ep        = pcie_tr.ep;
            attr1     = {pcie_tr.relaxed_ordering, pcie_tr.no_snoop};
            at        = pcie_tr.at;
            length    = pcie_tr.length;
            hdr[32*4-1 -: 32] = {fmt, pcie_type, r0, tc, r1, attr0, r2, th, td, ep, attr1, at, length};

            //RC
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
                hdr[32-1 : 0] = 'x;
                hdr[32*3-1 -: 64] = {completer_id, compl_status, bcm, byte_count, requester_id, tag, r0, lower_address};
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
                address      = pcie_cq.address;
                ph           = pcie_cq.ph;
                if (fmt[0] == 1'b0) begin
                    hdr[32-1 : 0] = 'x;
                    hdr[32*3-1 -: 64] = {requester_id, tag, lbe, fbe, address[32-1:2], ph};
                end else begin
                    hdr[32*3-1 -: 96] = {requester_id, tag, lbe, fbe, address, ph};
                end
            end

            prefix = '0;
            bar    =  0;
            req.data = {bar, prefix, hdr};
            finish_item(req);
        end
    endtask
endclass


