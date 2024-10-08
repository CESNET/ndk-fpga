// monitor.sv: pcie monitor 
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class monitor#(META_WIDTH_UP, META_WIDTH_DOWN) extends uvm_pcie::monitor;
    `uvm_component_param_utils(uvm_pcie_intel::monitor#(META_WIDTH_UP, META_WIDTH_DOWN));

    localparam int unsigned HDR_WIDTH       = 128;
    localparam int unsigned PREFIX_WIDTH    = 32;
    localparam int unsigned BAR_RANGE_WIDTH = 3;
    localparam ITEM_WIDTH = 32;
    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) avalon_up_data;
    uvm_tlm_analysis_fifo#(uvm_logic_vector::sequence_item#(META_WIDTH_UP))    avalon_up_meta;
    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) avalon_down_data;
    uvm_tlm_analysis_fifo#(uvm_logic_vector::sequence_item#(META_WIDTH_DOWN))  avalon_down_meta;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        avalon_up_data   = new("avalon_up_data",   this);
        avalon_up_meta   = new("avalon_up_meta",   this);
        avalon_down_data = new("avalon_down_data", this);
        avalon_down_meta = new("avalon_down_meta", this);
    endfunction

    task run_up();
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data;
        uvm_logic_vector::sequence_item#(META_WIDTH_UP)    meta;

        forever begin
            logic [HDR_WIDTH-1:0]    hdr;
            logic [PREFIX_WIDTH-1:0] prefix;
            logic [1-1: 0]           error;

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


            avalon_up_meta.get(meta);
            avalon_up_data.get(data);

            {error, prefix, hdr} = meta.data;
            {fmt, pcie_type, r0, tc, r1, attr0, r2, th, td, ep, attr1, at, length} = hdr[32*4-1 -: 32];
            //CC
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

                {completer_id, compl_status, bcm, byte_count, requester_id, tag, r0, lower_address} = hdr[32*3-1 -: 64];

                pcie_tr = uvm_pcie::completer_header::type_id::create("pcie_tr", this);
                pcie_tr.fmt               = fmt;
                pcie_tr.pcie_type         = pcie_type;
                pcie_tr.traffic_class     = tc;
                pcie_tr.id_based_ordering = attr1[0];
                pcie_tr.relaxed_ordering  = attr1[1];
                pcie_tr.no_snoop          = attr0[0];
                pcie_tr.th                = th;
                pcie_tr.td                = td;
                pcie_tr.ep                = ep;
                pcie_tr.at                = at;
                pcie_tr.length            = length;
                pcie_tr.completer_id      = completer_id;
                pcie_tr.compl_status      = compl_status;
                pcie_tr.bcm               = bcm;
                pcie_tr.byte_count        = byte_count;
                pcie_tr.requester_id      = requester_id;
                pcie_tr.tag               = tag;
                pcie_tr.lower_address     = lower_address;

                if (fmt[3-1:1] == 2'b01) begin
                    //avalon_up_data.get(data);
                    pcie_tr.data = new[length];
                    for (int unsigned it = 0; it < length; it++) begin
                        pcie_tr.data[it] = data.data[it];
                    end
                end

                cc_analysis_port.write(pcie_tr);
            //RQ
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
                    {requester_id, tag, lbe, fbe, address[32-1:2], ph} = hdr[32*3-1 -: 64];
                end else begin
                    {requester_id, tag, lbe, fbe, address, ph} = hdr[32*3-1 -: 96];
                end

                pcie_tr = uvm_pcie::request_header::type_id::create("pcie_tr", this);
                pcie_tr.fmt               = fmt;
                pcie_tr.pcie_type         = pcie_type;
                pcie_tr.traffic_class     = tc;
                pcie_tr.id_based_ordering = attr1[0];
                pcie_tr.relaxed_ordering  = attr1[1];
                pcie_tr.no_snoop          = attr0[0];
                pcie_tr.th                = th;
                pcie_tr.td                = td;
                pcie_tr.ep                = ep;
                pcie_tr.at                = at;
                pcie_tr.length            = length;
                pcie_tr.requester_id      = requester_id;
                pcie_tr.tag               = tag;
                pcie_tr.lbe               = lbe;
                pcie_tr.fbe               = fbe;
                pcie_tr.address           = address;
                pcie_tr.ph                = ph;

                if (fmt[3-1:1] == 2'b01) begin
                    //avalon_up_data.get(data);
                    pcie_tr.data = new[length];
                    for (int unsigned it = 0; it < length; it++) begin
                        pcie_tr.data[it] = data.data[it];
                    end
                end

                rq_analysis_port.write(pcie_tr);
            end
        end
    endtask


    task run_down();
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data;
        uvm_logic_vector::sequence_item#(META_WIDTH_DOWN)  meta;

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


            avalon_down_meta.get(meta);
            avalon_down_data.get(data);

            {bar, prefix, hdr} = meta.data;
            {fmt, pcie_type, r0, tc, r1, attr0, r2, th, td, ep, attr1, at, length} = hdr[32*4-1 -: 32];
            //RC
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

                {completer_id, compl_status, bcm, byte_count, requester_id, tag, r0, lower_address} = hdr[32*3-1 -: 64];

                pcie_tr = uvm_pcie::completer_header::type_id::create("pcie_tr", this);
                pcie_tr.fmt               = fmt;
                pcie_tr.pcie_type         = pcie_type;
                pcie_tr.traffic_class     = tc;
                pcie_tr.id_based_ordering = attr1[0];
                pcie_tr.relaxed_ordering  = attr1[1];
                pcie_tr.no_snoop          = attr0[0];
                pcie_tr.th                = th;
                pcie_tr.td                = td;
                pcie_tr.ep                = ep;
                pcie_tr.at                = at;
                pcie_tr.length            = length;
                pcie_tr.completer_id      = completer_id;
                pcie_tr.compl_status      = compl_status;
                pcie_tr.bcm               = bcm;
                pcie_tr.byte_count        = byte_count;
                pcie_tr.requester_id      = requester_id;
                pcie_tr.tag               = tag;
                pcie_tr.lower_address     = lower_address;

                if (fmt[3-1:1] == 2'b01) begin
                    //avalon_down_data.get(data);
                    pcie_tr.data = new[length];
                    for (int unsigned it = 0; it < length; it++) begin
                        pcie_tr.data[it] = data.data[it];
                    end
                end

                rc_analysis_port.write(pcie_tr);
            //CQ
            end else begin
                uvm_pcie_extend::request_header pcie_tr;
                logic [16-1:0] requester_id;
                logic [8-1:0]  tag;
                logic [4-1:0]  lbe;
                logic [4-1:0]  fbe;
                logic [64-1:2] address;
                logic [2-1:0]  ph;

                if (fmt[0] == 1'b0) begin
                    address[64-1:32] = 0;
                    {requester_id, tag, lbe, fbe, address[32-1:2], ph} = hdr[32*3-1 -: 64];
                end else begin
                    {requester_id, tag, lbe, fbe, address, ph} = hdr[32*3-1 -: 96];
                end

                pcie_tr = uvm_pcie_extend::request_header::type_id::create("pcie_tr", this);
                pcie_tr.fmt               = fmt;
                pcie_tr.pcie_type         = pcie_type;
                pcie_tr.traffic_class     = tc;
                pcie_tr.id_based_ordering = attr1[0];
                pcie_tr.relaxed_ordering  = attr1[1];
                pcie_tr.no_snoop          = attr0[0];
                pcie_tr.th                = th;
                pcie_tr.td                = td;
                pcie_tr.ep                = ep;
                pcie_tr.at                = at;
                pcie_tr.length            = length;
                pcie_tr.requester_id      = requester_id;
                pcie_tr.tag               = tag;
                pcie_tr.lbe               = lbe;
                pcie_tr.fbe               = fbe;
                pcie_tr.address           = address;
                pcie_tr.ph                = ph;
                pcie_tr.bar               = bar;
                pcie_tr.bar_aperture      = 26;
                pcie_tr.vf                = 0;

                if (fmt[3-1:1] == 2'b01) begin
                    //avalon_down_data.get(data);
                    pcie_tr.data = new[length];
                    for (int unsigned it = 0; it < length; it++) begin
                        pcie_tr.data[it] = data.data[it];
                    end
                end

                cq_analysis_port.write(pcie_tr);
            end
        end
    endtask

    task run_phase(uvm_phase phase);
        fork
            run_up();
            run_down();
        join
    endtask
endclass

