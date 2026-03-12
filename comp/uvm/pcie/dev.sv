// dev.sv: This is simulation of pcie device.
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

// This component is template for pcie device.
// Class contains structure which represent information required for responses
//


class pcie_info#(
    int unsigned TAG_WIDTH
);

    typedef struct {
        // This is info for sequece.
        // Sequence keep track what is generated
        // BE CAREFULL lower address is only 4 bist lower 2 bist
        // are count from fbe
        logic [7-1:2]  lower_address;
        logic [4-1:0]  fbe;
        logic [4-1:0]  lbe;
        int unsigned   rest_length; // in DWORS
        time           received_time; // simulation time when request have been received
    } req_info;

    req_info    request[logic [16-1:0]][logic [TAG_WIDTH-1:0]];
    //bar_config  bar;
    string name;

    function new(string name);
        this.name = name;
    endfunction

    function int unsigned request_num();
        int unsigned ret = 0;

        foreach(request[it]) begin
            ret += request[it].size();
        end
        return ret;
    endfunction

    function void request_register(logic [16-1:0] requester_id, logic [TAG_WIDTH-1:0] tag, req_info info);
        if (request.exists(requester_id) && request[requester_id].exists(tag)) begin
            `uvm_fatal(name, $sformatf("\n\tAlready registred request\n\t\trequest ID: 0x%h\n\t\tTAG: 0x%h(%d)",
                requester_id, tag, tag));
        end else begin
            request[requester_id][tag] = info;
        end
    endfunction


    function void request_delete(logic [16-1:0] requester_id, logic [TAG_WIDTH-1:0] tag);
         assert(request.exists(requester_id)) begin
             request[requester_id].delete(tag);
         end else begin
             `uvm_warning(name, $sformatf("\n\tResponse to unexisting requester id 0x%h", requester_id))
         end
    endfunction

    function void requester_add(logic [16-1:0] requester_id);
        if (!request.exists(requester_id)) begin
            request[requester_id].delete();
        end
    endfunction

    function void requester_remove(logic [16-1:0] requester_id);
        if (request[requester_id].size() != 0) begin
            string msg;

            msg = $sformatf("\n\tDeleter requester 0x%h which have pending reqeuest %0d",
                requester_id, request[requester_id].size());
            `uvm_warning(name, msg);
        end
        request.delete(requester_id);
    endfunction
endclass


//TODO: BASE DEV SHOULD DO NOTHING.
class dev extends uvm_component;
    `ndk_component_utils(uvm_pcie::dev)

    localparam TAG_WIDTH = 8;

    typedef dev this_type;
    uvm_analysis_imp#(uvm_pcie::header, this_type) port_pcie;

    // TODO: RESET
    //uvm_reset::sync_terminate reset_sync;

    // response info
    pcie_info#(TAG_WIDTH) rx_info;
    pcie_info#(TAG_WIDTH) tx_info;

    // Constructor
    function new(string name = "dev", uvm_component parent = null);
        super.new(name, parent);
        port_pcie = new("port_pcie", this);
        rx_info   = new({this.get_full_name(), ".rx_info"});
        tx_info   = new({this.get_full_name(), ".tx_info"});
    endfunction

    virtual function void register_pcie(uvm_pcie::root dev);
        `uvm_fatal(this.get_full_name(), "\n\tNOT IMPLEMENTED")
    endfunction

    virtual function void write(uvm_pcie::header tr);
        if (tr.fmt[3-1:1] == 2'b00 && tr.pcie_type[5-1:0] == 5'b00000) begin
            //Read request
            uvm_pcie::request_header req;
            pcie_info#(8)::req_info info;

            $cast(req, tr);

            info.lower_address = req.address[7-1:2];
            info.fbe = req.fbe;
            info.lbe = req.lbe;
            info.rest_length = req.length_get();
            info.received_time = $time;

            rx_info.request_register(req.requester_id, req.tag, info);
        end else if (tr.fmt[3-1:1] == 2'b01 && tr.pcie_type[5-1:0] == 5'b00000) begin
            //Write request
            ;
        end else if (tr.fmt[3-1:0] == 3'b010 && tr.pcie_type[5-1:0] == 5'b01010) begin
            // Response
            int unsigned move;
            int unsigned length;
            int unsigned byte_count;
            uvm_pcie::completer_header comp;

            $cast(comp, tr);
            length = tr.length != 0 ? tr.length : 1024;
            move   = comp.lower_address & 2'b11;
            byte_count = comp.byte_count != 0 ? comp.byte_count : 4096;
            //if completed the nremove tag
            if (byte_count <= (length*4 - move)) begin
                tx_info.request_delete(comp.requester_id, comp.tag);
            end
        end else begin
            const string msg = $sformatf("\n\tBehavioral for header is not implemented!!%s", tr.convert2string());
            `uvm_fatal(this.get_full_name(), msg);
        end
    endfunction
endclass

