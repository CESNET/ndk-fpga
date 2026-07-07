// sequence.sv: sequence
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_resp extends uvm_sequence #(uvm_pcie::header);
    `uvm_object_utils(uvm_pcie_dma_cq::sequence_resp)

    localparam MAX_REQUEST_SIZE = 128;
    localparam MAX_PAYLOAD_SIZE = 64;

    int unsigned response_only;
    rand int unsigned transactions;
    protected uvm_pcie::pcie_info   info;

    constraint const_base {
        transactions   inside {[200:1000]};
    }

    function new(string name = "sequence_base");
        super.new(name);
    endfunction

    function void response_handler(uvm_sequence_item response);
        //uvm_pcie::header hdr;

        //if ($cast(hdr, response)) begin
        //end

        //$write("TEST AAA%s\n", response.convert2string());
    endfunction

    virtual function void mid_do(uvm_sequence_item     this_item);
        uvm_pcie::header hdr;

        $cast(hdr, this_item);
        if (hdr.hdr_type == uvm_pcie::header::RQ_HDR) begin
            uvm_pcie::request_header cq_hdr;

            $cast(cq_hdr, hdr);
            if (cq_hdr.fmt[2:1] == 2'b00) begin
                info.cq_tag_add(cq_hdr.requester_id, cq_hdr.tag);
            end
        end else if (hdr.hdr_type == uvm_pcie::header::COMPLETER_HDR) begin
            //uvm_pcie::completer_header rc_hdr;
            //$cast(rc_hdr, hdr);
        end
    endfunction

    // In body you have to define how the MFB data will looks like
    task body;
        uvm_common::sequence_cfg state;
        int unsigned it = 0;

        assert(uvm_config_db #(uvm_pcie::pcie_info)::get(m_sequencer, "", "pcie_info", info)) else begin
            `uvm_fatal(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get tag manager");
        end;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        //use_response_handler(1);

        it = 0;
        //TODO: improve stopping sequence removing emtpy cicle when there there is empty rq_hdr fifo and request only set.
        while (it < transactions /*&& (state == null || state.next())*/) begin
            uvm_pcie::completer_header rc_hdr;
            int unsigned cq_num;
            int unsigned byte_count;
            int unsigned cc_length;
            const int unsigned max_payload = MAX_PAYLOAD_SIZE < 1024 ? MAX_PAYLOAD_SIZE : 0;


            wait (info.rq_hdr.size() != 0);


            //cc_hdr = hdr.pop_front();
            //Cahnge randomize to 0 gauss distribution. when head have the moust generated top transaction
            cq_num = $urandom_range(0, info.rq_hdr.size()-1);
            rc_hdr = uvm_pcie::completer_header::type_id::create("rc_hdr", m_sequencer);

            //
            start_item(rc_hdr);
            assert(rc_hdr.randomize() with {
                rc_hdr.data.size() <= 15000;
                info.rq_hdr[cq_num].rest_length >= MAX_PAYLOAD_SIZE ->
                rc_hdr.length dist {
                    max_payload :/60,
                    [6*MAX_PAYLOAD_SIZE/8:MAX_PAYLOAD_SIZE-1] :/ 30,
                    [MAX_PAYLOAD_SIZE/8:6*MAX_PAYLOAD_SIZE/8-1] :/ 10,
                    [1:MAX_PAYLOAD_SIZE/8-1] :/ 10
                };
                info.rq_hdr[cq_num].rest_length < MAX_PAYLOAD_SIZE ->
                rc_hdr.length dist {
                    info.rq_hdr[cq_num].rest_length  :/70,
                    [1:info.rq_hdr[cq_num].rest_length] :/ 30
                };

                (rc_hdr.length == 0) -> (rc_hdr.data.size() == 1024);
                (rc_hdr.length != 0) -> (rc_hdr.data.size() == rc_hdr.length);
                rc_hdr.compl_status == 3'b000; //change in future. to generate some errors
                solve rc_hdr.length before rc_hdr.data;
            }) else begin
                `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize rc HEADER");
            end


            rc_hdr.fmt           = 3'b010;
            rc_hdr.pcie_type     = 5'b01010;
            rc_hdr.ep            = 0;
            rc_hdr.at            = 0;
            rc_hdr.completer_id  = 0;
            rc_hdr.requester_id  = info.rq_hdr[cq_num].hdr.requester_id;
            rc_hdr.tag           = info.rq_hdr[cq_num].hdr.tag;
            rc_hdr.bcm           = 0;
            rc_hdr.lower_address = info.rq_hdr[cq_num].lower_address;
            rc_hdr.byte_count    = info.rq_hdr[cq_num].byte_count;

            finish_item(rc_hdr);

            cc_length = (rc_hdr.length != 0) ? rc_hdr.length : 1024;

            //Remove REQUEST if there is
            if (info.rq_hdr[cq_num].rest_length  <= cc_length) begin
                assert(cc_length*4 >= info.rq_hdr[cq_num].byte_count) else begin
                    `uvm_fatal(this.get_full_name(), "\n\tFAiled count byte_count and length in requeste header");
                end
                info.rq_hdr.delete(cq_num);
            end else begin
                info.rq_hdr[cq_num].rest_length   -= cc_length;
                info.rq_hdr[cq_num].byte_count    -= (cc_length*4 - (info.rq_hdr[cq_num].lower_address & 2'b11));
                info.rq_hdr[cq_num].lower_address  = info.rq_hdr[cq_num].lower_address & ~64'b11 + cc_length*4;
            end

            it++;
        end
    endtask

endclass


