// sequence.sv: complletition
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Random request response sequence.
// One request response sequence
// Small response X huge response
// NO RESPONSE

/////////////////////////////////////////////////////////////////////////
// BASE SEQUENCE
/////////////////////////////////////////////////////////////////////////
virtual class sequence_comp extends uvm_common::sequence_base #(config_sequence, uvm_pcie::header);

    // SET DEV ID TO 0
    // RESPONSE SHOULD be with different ID
    // BUT response on same RQ should be with same ID
    // rand logic [16-1:0] dev_id[];

    localparam TAG_WIDTH = 8;
    localparam RCB       = 64/4; //divided response in DWORD

    rand int unsigned transactions;
    rand int unsigned length_max;
    rand int unsigned length_min;

    protected pcie_info#(TAG_WIDTH)   info;

    function new(string name);
        super.new(name);
        info = null;
    endfunction

    function logic [TAG_WIDTH-1:0] reqs_tag_fist_get(logic [16-1:0] dev_id);
        logic [TAG_WIDTH-1:0] tag;
        time min;

        info.request[dev_id].first(tag);
        min = info.request[dev_id][tag].received_time;
        foreach (info.request[dev_id][it]) begin
            const time tmp_time = info.request[dev_id][it].received_time;
            if (min > tmp_time) begin
                min = tmp_time;
                tag = it;
            end
        end

        return tag;
    endfunction

    function uvm_pcie::completer_header comp_hdr_randomize(logic [16-1:0] dev_id, logic [TAG_WIDTH-1:0] tag_gen);
        logic [2-1:0] fbe_addr;
        uvm_pcie::completer_header rc_hdr;
        pcie_info#(TAG_WIDTH)::req_info rc_info;

        rc_hdr  = uvm_pcie::completer_header::type_id::create("res_hdr", m_sequencer);

        if (info != null) begin
            rc_info = info.request[dev_id][tag_gen];
            fbe_addr = uvm_pcie::encode_fbe(rc_info.fbe);
        end

        assert(rc_hdr.randomize() with {
            // constraint boundary should be divided on address divided by
            // 64
            // -> ((rc_hdr.lower_address + rc_hdr.length) % RCB) == 0; //in

            if (info != null) {
                rc_hdr.lower_address == {rc_info.lower_address, fbe_addr};
                rc_hdr.data.size()   <= rc_info.rest_length;
                (rc_info.rest_length <= length_min) -> rc_hdr.data.size() == rc_info.rest_length;
                (rc_info.rest_length > length_min && rc_info.rest_length <= length_max) -> rc_hdr.data.size() inside {[length_min:rc_info.rest_length]};
                (rc_info.rest_length > length_max) -> rc_hdr.data.size() inside {[length_min:length_max]};
                rc_hdr.tag           == tag_gen;
                rc_hdr.requester_id  == dev_id;
            } else {
                rc_hdr.data.size() inside {[length_min:length_max]};
                rc_hdr.byte_count >= rc_hdr.data.size()*4;
            }

            (rc_hdr.data.size() == 1024)-> (rc_hdr.length == 0);
            (rc_hdr.data.size() <  1024)-> (rc_hdr.length == rc_hdr.data.size());


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
        rc_hdr.bcm           = 0;

        if (info != null) begin
            if (rc_info.rest_length == 1 && rc_info.fbe == 0 && rc_info.lbe == 0) begin
                rc_hdr.byte_count =  1;
            end else begin
                rc_hdr.byte_count =  unsigned'(rc_info.rest_length * 4) - unsigned'(uvm_pcie::encode_fbe(rc_info.fbe)) - (4-unsigned'(uvm_pcie::encode_lbe(rc_info.lbe)));
            end

            rc_info.fbe           = '1;
            rc_info.lower_address += rc_hdr.length;
            rc_info.rest_length   -= rc_hdr.length;

            if (rc_info.rest_length > 0) begin
                info.request[rc_hdr.requester_id][rc_hdr.tag] = rc_info;
            end else begin
                info.request_delete(rc_hdr.requester_id, rc_hdr.tag);
            end
        end

        return rc_hdr;
    endfunction

endclass

/////////////////////////////////////////////////////////////////////////
// Simple sequence
/////////////////////////////////////////////////////////////////////////
class sequence_comp_base extends sequence_comp;
    `uvm_object_utils(uvm_pcie::sequence_comp_base)

    rand enum {TAG_SEL_RAND, TAG_SEL_FIRST} tag_sel;

    constraint const_base {
        transactions   inside {[5:200]};
        //dev_id.size()  inside {[1:10]};
    }

    //cfg.payload_size_max
    //In Dwords
    constraint c_length {
        length_min <= length_max;
        length_min dist {
            [cfg.payload_size_min                                                   : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*1/8] :/27,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*1/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*2/8] :/13,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*2/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*3/8] :/5,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*3/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*4/8] :/2,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*4/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*5/8] :/2,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*5/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*6/8] :/8,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*6/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*7/8] :/13,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*7/8 : cfg.payload_size_max                                                  ] :/27
        };
        length_max dist {
            [cfg.payload_size_min                                                   : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*1/8] :/27,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*1/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*2/8] :/13,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*2/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*3/8] :/5,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*3/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*4/8] :/2,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*4/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*5/8] :/2,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*5/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*6/8] :/8,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*6/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*7/8] :/13,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*7/8 : cfg.payload_size_max                                                  ] :/27
        };
    }

    function new(string name = "sequence_comp_base");
        super.new(name);
    endfunction

    // In body you have to define how the MFB data will looks like
    task body;
        uvm_common::sequence_cfg state;
        int unsigned it = 0;

        // GET information about request
        if(!uvm_config_db #(pcie_info#(TAG_WIDTH))::get(m_sequencer, "", "pcie_info", info)) begin
            info = null;
            `uvm_warning(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get tag manager");
        end;

        // GET state
        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        it = 0;
        while (it < transactions && (state == null || state.next())) begin
            logic [TAG_WIDTH-1:0] tag_gen;
            logic [16-1:0] devs_id[];
            logic [16-1:0] dev_id;
            uvm_pcie::completer_header rc_hdr;

            if (info != null) begin
                do begin
                    devs_id = info.request.find_index() with (item.size() > 0);
                    if (devs_id.size() == 0) begin
                        #(100ns);
                    end
                end while(devs_id.size() == 0);

                assert(std::randomize(dev_id)  with {dev_id  inside {devs_id};});
                if (tag_sel == TAG_SEL_RAND) begin
                    assert(std::randomize(tag_gen) with {tag_gen inside {info.request[dev_id].find_index() with (1'b1)};});
                end else begin
                    // FIND FIRST SEND TAG
                    tag_gen = reqs_tag_fist_get(dev_id);
                end
            end

            req = comp_hdr_randomize(dev_id, tag_gen);
            start_item(req);
            finish_item(req);
            it++;
        end
    endtask
endclass

/////////////////////////////////////////////////////////////////////////
// SEQUENCE DOESNT SEND ANY RESPONSES
/////////////////////////////////////////////////////////////////////////
class sequence_comp_stop extends uvm_common::sequence_base #(config_sequence, uvm_pcie::header);
    `uvm_object_param_utils(uvm_pcie::sequence_comp_stop)

    rand int unsigned time_sleep; //in NS

    constraint const_base {
        time_sleep dist {
            [10:20]  :/30,
            [20:100] :/20,
            [100:1000] :/5
        };
    }

    function new(string name = "sequence_comp_stop");
        super.new(name);
    endfunction

    task body;
        //Just sleep
        #(time_sleep*1ns);
    endtask
endclass

/////////////////////////////////////////////////////////////////////////
//SEND COPLETER WITH SMALL RESPONSES
/////////////////////////////////////////////////////////////////////////
class sequence_comp_small extends sequence_comp;
    `uvm_object_param_utils(uvm_pcie::sequence_comp_small)

    rand enum {TAG_SEL_RAND, TAG_SEL_FIRST} tag_sel;

    constraint const_base {
        transactions   inside {[10:250]};
        //dev_id.size()  inside {[1:10]};
    }

    //cfg.payload_size_max
    //In Dwords
    constraint c_length {
        length_min == cfg.payload_size_min;
        length_max == cfg.payload_size_min;
    }

    function new(string name = "sequence_comp_small");
        super.new(name);
    endfunction

    task body;
        uvm_common::sequence_cfg state;
        int unsigned it = 0;

        // GET information about request
        if(!uvm_config_db #(pcie_info#(TAG_WIDTH))::get(m_sequencer, "", "pcie_info", info)) begin
            info = null;
            `uvm_warning(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get tag manager");
        end;

        // GET state
        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        it = 0;
        while (it < transactions && (state == null || state.next())) begin
            logic [TAG_WIDTH-1:0] tag_gen;
            logic [16-1:0] devs_id[];
            logic [16-1:0] dev_id;
            uvm_pcie::completer_header rc_hdr;

            if (info != null) begin
                do begin
                    devs_id = info.request.find_index() with (item.size() > 0);
                    if (devs_id.size() == 0) begin
                        #(100ns);
                    end
                end while(devs_id.size() == 0);

                assert(std::randomize(dev_id)  with {dev_id  inside {devs_id};});
                if (tag_sel == TAG_SEL_RAND) begin
                    assert(std::randomize(tag_gen) with {tag_gen inside {info.request[dev_id].find_index() with (1'b1)};});
                end else begin
                    // FIND FIRST SEND TAG
                    tag_gen = reqs_tag_fist_get(dev_id);
                end
            end

            req = comp_hdr_randomize(dev_id, tag_gen);
            start_item(req);
            finish_item(req);
            it++;
        end
    endtask
endclass

/////////////////////////////////////////////////////////////////////////
//SEND COPLETER WITH big
/////////////////////////////////////////////////////////////////////////
class sequence_comp_big extends sequence_comp;
    `uvm_object_param_utils(uvm_pcie::sequence_comp_big)

    rand enum {TAG_SEL_RAND, TAG_SEL_FIRST} tag_sel;

    constraint const_base {
        transactions   inside {[1:35]};
        //dev_id.size()  inside {[1:10]};
    }

    //cfg.payload_size_max
    //In Dwords
    constraint c_length {
        length_min == cfg.payload_size_max;
        length_max == cfg.payload_size_max;
    }

    function new(string name = "sequence_comp_big");
        super.new(name);
    endfunction

    task body;
        uvm_common::sequence_cfg state;
        int unsigned it = 0;

        // GET information about request
        if(!uvm_config_db #(pcie_info#(TAG_WIDTH))::get(m_sequencer, "", "pcie_info", info)) begin
            info = null;
            `uvm_warning(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get tag manager");
        end;

        // GET state
        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        it = 0;
        while (it < transactions && (state == null || state.next())) begin
            logic [TAG_WIDTH-1:0] tag_gen;
            logic [16-1:0] devs_id[];
            logic [16-1:0] dev_id;
            uvm_pcie::completer_header rc_hdr;

            if (info != null) begin
                do begin
                    devs_id = info.request.find_index() with (item.size() > 0);
                    if (devs_id.size() == 0) begin
                        #(100ns);
                    end
                end while(devs_id.size() == 0);

                assert(std::randomize(dev_id)  with {dev_id  inside {devs_id};});
                if (tag_sel == TAG_SEL_RAND) begin
                    assert(std::randomize(tag_gen) with {tag_gen inside {info.request[dev_id].find_index() with (1'b1)};});
                end else begin
                    // FIND FIRST SEND TAG
                    tag_gen = reqs_tag_fist_get(dev_id);
                end
            end

            req = comp_hdr_randomize(dev_id, tag_gen);
            start_item(req);
            finish_item(req);
            it++;
        end
    endtask
endclass


/////////////////////////////////////////////////////////////////////////
//SEND COPLETER WITH response on one tag
/////////////////////////////////////////////////////////////////////////
class sequence_comp_one_tag extends sequence_comp;
    `uvm_object_param_utils(uvm_pcie::sequence_comp_one_tag)

    rand enum {TAG_SEL_RAND, TAG_SEL_FIRST} tag_sel;

    constraint const_base {
        transactions   inside {[5:50]};
        //dev_id.size()  inside {[1:10]};
    }

    //cfg.payload_size_max
    //In Dwords
    constraint c_length {
        length_min <= length_max;
        length_min dist {
            [cfg.payload_size_min                                                   : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*1/8] :/27,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*1/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*2/8] :/13,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*2/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*3/8] :/5,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*3/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*4/8] :/2,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*4/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*5/8] :/2,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*5/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*6/8] :/8,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*6/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*7/8] :/13,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*7/8 : cfg.payload_size_max                                                  ] :/27
        };
        length_max dist {
            [cfg.payload_size_min                                                   : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*1/8] :/27,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*1/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*2/8] :/13,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*2/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*3/8] :/5,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*3/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*4/8] :/2,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*4/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*5/8] :/2,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*5/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*6/8] :/8,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*6/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*7/8] :/13,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*7/8 : cfg.payload_size_max                                                  ] :/27
        };
    }

    function new(string name = "sequence_comp_one_tag");
        super.new(name);
    endfunction

    task body;
        uvm_common::sequence_cfg state;
        int unsigned it = 0;

        // GET information about request
        if(!uvm_config_db #(pcie_info#(TAG_WIDTH))::get(m_sequencer, "", "pcie_info", info)) begin
            info = null;
            `uvm_warning(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get tag manager");
        end;

        // GET state
        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        it = 0;
        while (it < transactions && (state == null || state.next())) begin
            logic [TAG_WIDTH-1:0] tag_gen;
            logic [16-1:0] devs_id[];
            logic [16-1:0] dev_id;
            uvm_pcie::completer_header rc_hdr;

            if (info != null) begin
                do begin
                    devs_id = info.request.find_index() with (item.size() > 0);
                    if (devs_id.size() == 0) begin
                        #(100ns);
                    end
                end while(devs_id.size() == 0);

                assert(std::randomize(dev_id)  with {dev_id  inside {devs_id};});
                if (tag_sel == TAG_SEL_RAND) begin
                    assert(std::randomize(tag_gen) with {tag_gen inside {info.request[dev_id].find_index() with (1'b1)};});
                end else begin
                    // FIND FIRST SEND TAG
                    tag_gen = reqs_tag_fist_get(dev_id);
                end
            end

            // Until send All responses
            // If there is no info then we dont care about matching request.
            while ((info == null || info.request[dev_id].exists(tag_gen) == 1) &&
                   it < transactions && (state == null || state.next())
            ) begin
                req = comp_hdr_randomize(dev_id, tag_gen);
                start_item(req);
                finish_item(req);
                it++;
            end
        end
    endtask
endclass


/////////////////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY COMPL
/////////////////////////////////////////////////////////////////////////
class sequence_comp_lib extends uvm_common::sequence_library#(config_sequence, uvm_pcie::header);
  `uvm_object_param_utils(uvm_pcie::sequence_comp_lib)
  `uvm_sequence_library_utils(uvm_pcie::sequence_comp_lib)

  function new(string name = "sequence_lib_tx");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(uvm_pcie::sequence_comp_base::get_type());
        this.add_sequence(uvm_pcie::sequence_comp_stop::get_type());
        this.add_sequence(uvm_pcie::sequence_comp_small::get_type());
        this.add_sequence(uvm_pcie::sequence_comp_big::get_type());
        this.add_sequence(uvm_pcie::sequence_comp_one_tag::get_type());
    endfunction
endclass


