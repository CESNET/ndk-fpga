// sequence.sv: sequence
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_base extends uvm_sequence #(uvm_pcie::header);
    `uvm_object_utils(uvm_pcie::sequence_base)

    localparam MAX_REQUEST_SIZE = 128;
    localparam MAX_PAYLOAD_SIZE = 64;

    rand logic [16-1:0] dev_id[];

    int unsigned response_only;
    rand int unsigned transactions;
    protected pcie_info   info;

    constraint const_base {
        transactions   inside {[200:1000]};
        dev_id.size()  inside {[1:10]};
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

    virtual function void mid_do(uvm_sequence_item 	this_item);
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
        logic cq;

        assert(uvm_config_db #(pcie_info)::get(m_sequencer, "", "pcie_info", info)) else begin
            `uvm_fatal(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get tag manager");
        end;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        //create tag
        for (int unsigned it = 0; it < dev_id.size(); it++) begin
            info.requester_add(dev_id[it]);
        end

        //use_response_handler(1);

        it = 0;
        //TODO: improve stopping sequence removing emtpy cicle when there there is empty rq_hdr fifo and request only set.
        while (it < (transactions*4) /*&& (state == null || state.next())*/) begin
            //assert(std::randomize(rq))
            //generate CQ nebo RC
            std::randomize(cq) with { cq dist {1'b1 :/ 5,  1'b0 :/ info.rq_hdr.size()}; };
            if (cq == 1 && response_only == 0) begin
                logic [16-1:0] dev_id_act;
                uvm_pcie::request_header cq_hdr;

                std::randomize(dev_id_act) with {dev_id_act inside {dev_id};};
                wait (info.cq_tags[dev_id_act].size() < 256);

                cq_hdr = uvm_pcie::request_header::type_id::create("cq_hdr", m_sequencer);
                start_item(cq_hdr);
                assert(cq_hdr.randomize() with {
                    cq_hdr.ph == 0;
                    if (cq_hdr.length == 1) {
                        cq_hdr.fbe inside {4'b1001, 4'b0101, 4'b1010, 4'b0011, 4'b0110, 4'b1100, 4'b0001, 4'b0010, 4'b0100, 4'b1000};
                        //cq_hdr.fbe inside {4'b1001, 4'b0101, 4'b1010, 4'b0011, 4'b0110, 4'b1100, 4'b0001, 4'b0010, 4'b0100, 4'b1000, 4'b0000};
                        cq_hdr.lbe == 4'b0000;
                    } else {
                        cq_hdr.fbe inside {4'b0001, 4'b0011, 4'b0111, 4'b1111};
                        cq_hdr.lbe inside {4'b1111, 4'b1110, 4'b1100, 4'b1000};
                    }
                    cq_hdr.fmt[0] == 1'b0 -> cq_hdr.address[64-1:32] == 0;
                    //TODO: change to original
                    //cq_hdr.fmt[2:1]  dist {2'b00 :/ 45, 2'b01 :/ 45, [2'b00:2'b11]  :/ 10}; // 2'b00 => read,  2'b01 => write
                    cq_hdr.fmt[2:1]  dist {2'b00 :/ 45, 2'b01 :/ 45}; // 2'b00 => read,  2'b01 => write
                    //TODO: change to original
                    //cq_hdr.pcie_type dist {5'b00000 :/ 95, [5'b00000:5'b11111] :/ 5};
                    cq_hdr.pcie_type == 0;
                    //TODO: remove this // if read then length is lower that 32 DWORDS
                    cq_hdr.fmt[2:1] == 2'b00 -> (cq_hdr.length <= MAX_REQUEST_SIZE && cq_hdr.length > 0); //read
                    cq_hdr.fmt[2:1] == 2'b00 -> (cq_hdr.length <= 32 && cq_hdr.length > 0); //read
                    cq_hdr.fmt[2:1] == 2'b01 -> (cq_hdr.length <= MAX_PAYLOAD_SIZE && cq_hdr.length > 0); //write


                    cq_hdr.requester_id == dev_id_act;
                    cq_hdr.tag inside   {[0:2**8-1]};  // 8 bit tag
                    !(cq_hdr.tag inside {info.cq_tags[cq_hdr.requester_id]}); //tag is not in array
                }) else begin
                    `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize cq header");
                end
                cq_hdr.th  = 0;
                cq_hdr.td  = 0;
                cq_hdr.ep  = 0;
                finish_item(cq_hdr);
                cq++;
            end

            if (cq == 0 && info.rq_hdr.size() != 0) begin
                uvm_pcie::completer_header rc_hdr;
                int unsigned rq_num;
                int unsigned byte_count;
                int unsigned rc_length;
                const int unsigned max_payload = MAX_PAYLOAD_SIZE < 1024 ? MAX_PAYLOAD_SIZE : 0;


                //cc_hdr = hdr.pop_front();
                rq_num = $urandom_range(0, info.rq_hdr.size()-1); //Cahnge randomize to 0 gauss distribution. when head have the moust generated top transaction
                rc_hdr = uvm_pcie::completer_header::type_id::create("cc_hdr", m_sequencer);

                //
                start_item(rc_hdr);
                assert(rc_hdr.randomize() with {
                    rc_hdr.data.size() <= 15000;
                    info.rq_hdr[rq_num].rest_length >= MAX_PAYLOAD_SIZE -> rc_hdr.length dist {max_payload :/60,  [6*MAX_PAYLOAD_SIZE/8:MAX_PAYLOAD_SIZE-1] :/ 30,  [MAX_PAYLOAD_SIZE/8:6*MAX_PAYLOAD_SIZE/8-1] :/ 10,  [1:MAX_PAYLOAD_SIZE/8-1] :/ 10};
                    info.rq_hdr[rq_num].rest_length <  MAX_PAYLOAD_SIZE -> rc_hdr.length dist {info.rq_hdr[rq_num].rest_length  :/70,  [1:info.rq_hdr[rq_num].rest_length] :/ 30};

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
                rc_hdr.requester_id  = 0;
                rc_hdr.tag           = info.rq_hdr[rq_num].hdr.tag;
                rc_hdr.bcm           = 0;
                rc_hdr.lower_address = info.rq_hdr[rq_num].lower_address;
                rc_hdr.byte_count    = info.rq_hdr[rq_num].byte_count;

                finish_item(rc_hdr);

                rc_length = (rc_hdr.length != 0) ? rc_hdr.length : 1024;

                //Remove REQUEST if there is
                if (info.rq_hdr[rq_num].rest_length  <= rc_length) begin
                    assert(rc_length*4 >= info.rq_hdr[rq_num].byte_count) else begin
                        `uvm_fatal(this.get_full_name(), "\n\tFAiled count byte_count and length in requeste header");
                    end
                    info.rq_hdr.delete(rq_num);
                end else begin
                    info.rq_hdr[rq_num].rest_length   -= rc_length;
                    info.rq_hdr[rq_num].byte_count    -= (rc_length*4 - (info.rq_hdr[rq_num].lower_address & 2'b11));
                    info.rq_hdr[rq_num].lower_address  = info.rq_hdr[rq_num].lower_address & ~64'b11;
                end
            end

            it++;
        end
    endtask

endclass




