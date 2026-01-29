// sequence.sv: sequence
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


// REQUEST + TAG => A lot of requester with same tag
//               => One requester a lot of tags
//               => few requester
//
// Request size  => a lot of small request
//               => Maximal requests
//               => Random requests
// NO REQUEST

class sequence_request extends uvm_common::sequence_base #(config_sequence, uvm_pcie::header);
    `uvm_object_param_utils(uvm_pcie::sequence_request)

    localparam TAG_WIDTH = 8;

    localparam BAR0_BASE_ADDR    = 32'h01000000;
    localparam BAR1_BASE_ADDR    = 32'h02000000;
    localparam BAR2_BASE_ADDR    = 32'h03000000;
    localparam BAR3_BASE_ADDR    = 32'h04000000;
    localparam BAR4_BASE_ADDR    = 32'h05000000;
    localparam BAR5_BASE_ADDR    = 32'h06000000;
    localparam EXP_ROM_BASE_ADDR = 32'h0A000000;


    rand logic [16-1:0] dev_id[];
    rand int unsigned transactions;
    rand int unsigned bar_probability[];

    rand int unsigned request_length_min;
    rand int unsigned request_length_max;
    rand int unsigned payload_length_min;
    rand int unsigned payload_length_max;

    protected pcie_info#(TAG_WIDTH)   info;

    constraint const_base {
        transactions   inside {[50:100]};
        dev_id.size()  inside {[1:10]};
        bar_probability.size() == 7+1; // BAR number + 1
        bar_probability.sum() > 0;
        foreach(bar_probability[it]) {
            bar_probability[it] <= 50;
        }
    }

    //In Dwords
    constraint c_length {
        request_length_min <= request_length_max;
        request_length_min dist {
            [cfg.request_size_min                                                   : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*1/8] :/27,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*1/8 : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*2/8] :/13,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*2/8 : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*3/8] :/5,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*3/8 : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*4/8] :/2,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*4/8 : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*5/8] :/2,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*5/8 : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*6/8] :/8,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*6/8 : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*7/8] :/13,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*7/8 : cfg.request_size_max                                                  ] :/27
        };
        request_length_max dist {
            [cfg.request_size_min                                                   : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*1/8] :/27,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*1/8 : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*2/8] :/13,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*2/8 : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*3/8] :/5,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*3/8 : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*4/8] :/2,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*4/8 : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*5/8] :/2,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*5/8 : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*6/8] :/8,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*6/8 : cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*7/8] :/13,
            [cfg.request_size_min + (cfg.request_size_max-cfg.request_size_min)*7/8 : cfg.request_size_max                                                  ] :/27
        };

        payload_length_min <= payload_length_max;
        payload_length_min dist {
            [cfg.payload_size_min                                                   : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*1/8] :/27,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*1/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*2/8] :/13,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*2/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*3/8] :/5,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*3/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*4/8] :/2,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*4/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*5/8] :/2,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*5/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*6/8] :/8,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*6/8 : cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*7/8] :/13,
            [cfg.payload_size_min + (cfg.payload_size_max-cfg.payload_size_min)*7/8 : cfg.payload_size_max                                                  ] :/27
        };
        payload_length_max dist {
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

    function new(string name = "sequence_base");
        super.new(name);
    endfunction

    // In body you have to define how the MFB data will looks like
    task body;
        uvm_common::sequence_cfg state;
        int unsigned it = 0;

        if(!uvm_config_db #(pcie_info#(TAG_WIDTH))::get(m_sequencer, "", "pcie_info", info)) begin
            `uvm_warning(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get tag manager");
            info = null;
        end;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        it = 0;
        while (it < transactions && (state == null || state.next())) begin
            logic [16-1:0] dev_id_act;
            logic [TAG_WIDTH-1:0]  used_tag[$];
            uvm_pcie::request_header cq_hdr;

            assert(std::randomize(dev_id_act) with {dev_id_act inside {dev_id};}) else begin
                `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize device id");
            end

            if (info != null) begin
                info.requester_add(dev_id_act);
                wait (info.request[dev_id_act].size() < 256);
                used_tag = info.request[dev_id_act].find_index() with (1'b1);
            end else begin
                used_tag = {};
            end

            cq_hdr = uvm_pcie::request_header::type_id::create("cq_hdr", m_sequencer);
            start_item(cq_hdr);

            assert(cq_hdr.randomize() with {
                cq_hdr.ph == 0;
                if (cq_hdr.length == 1) {
                    // When lenght is 1 then all fbe value should be supported
                    //cq_hdr.fbe inside {4'b1110, 4'b0111, 4'b1001, 4'b0101, 4'b1010, 4'b0011, 4'b0110, 4'b1100, 4'b0001, 4'b0010, 4'b0100, 4'b1000};
                    //cq_hdr.fbe inside {4'b1001, 4'b0101, 4'b1010, 4'b0011, 4'b0110, 4'b1100, 4'b0001, 4'b0010, 4'b0100, 4'b1000, 4'b0000};
                    cq_hdr.lbe == 4'b0000;
                } else {
                    cq_hdr.fbe inside {4'b1000, 4'b1100, 4'b1110, 4'b1111};
                    cq_hdr.lbe inside {4'b1111, 4'b0111, 4'b0011, 4'b0001};
                }

                cq_hdr.fmt[0] == 1'b0 -> cq_hdr.address[32-1:2] dist {[0             :BAR0_BASE_ADDR] :/ bar_probability[0],
                                                                      [BAR0_BASE_ADDR:BAR1_BASE_ADDR-1] :/ bar_probability[1],
                                                                      [BAR1_BASE_ADDR:BAR2_BASE_ADDR-1] :/ bar_probability[2],
                                                                      [BAR2_BASE_ADDR:BAR3_BASE_ADDR-1] :/ bar_probability[3],
                                                                      [BAR3_BASE_ADDR:BAR4_BASE_ADDR-1] :/ bar_probability[4],
                                                                      [BAR4_BASE_ADDR:BAR5_BASE_ADDR-1] :/ bar_probability[5],
                                                                      [BAR5_BASE_ADDR:EXP_ROM_BASE_ADDR-1] :/ bar_probability[6],
                                                                      [EXP_ROM_BASE_ADDR:32'hffffffff]  :/ bar_probability[7]
                                                                  };
                cq_hdr.fmt[0] == 1'b0 -> cq_hdr.address[64-1:32] == 0;
                cq_hdr.fmt[0] dist {1'b0 :/ 70, 1'b1 :/ 30};
                //TODO: change to original
                //cq_hdr.fmt[2:1]  dist {2'b00 :/ 45, 2'b01 :/ 45, [2'b00:2'b11]  :/ 10}; // 2'b00 => read,  2'b01 => write
                cq_hdr.fmt[2:1]  dist {2'b00 :/ 45, 2'b01 :/ 45}; // 2'b00 => read,  2'b01 => write
                //TODO: change to original
                //cq_hdr.pcie_type dist {5'b00000 :/ 95, [5'b00000:5'b11111] :/ 5};
                cq_hdr.pcie_type == 0;
                //READ REQUEST
                if (cq_hdr.fmt[2:1] == 2'b00) {
                    cq_hdr.data.size() == 0;
                    request_length_max == 1024 -> cq_hdr.length inside {[request_length_min:request_length_max-1], 0};
                    request_length_max != 1024 -> cq_hdr.length inside {[request_length_min:request_length_max]};
                    cq_hdr.tag < 2**TAG_WIDTH;
                    !(cq_hdr.tag inside {used_tag});
                }
                //WRITE request
                if (cq_hdr.fmt[2:1] == 2'b01) {
                    cq_hdr.data.size() inside {[payload_length_min:payload_length_max]};
                    cq_hdr.data.size() == 1024 -> (cq_hdr.length == 0);
                    cq_hdr.data.size() != 1024 -> (cq_hdr.length == cq_hdr.data.size());
                    //Write request don care about tag
                }

                cq_hdr.requester_id == dev_id_act;
                solve cq_hdr.fmt before cq_hdr.data;
            }) else begin
                `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize cq header");
            end
            cq_hdr.th  = 0;
            cq_hdr.td  = 0;
            cq_hdr.ep  = 0;

            //ADD -> READ request
            if (info != null && cq_hdr.fmt[2:1] == 2'b00) begin
                pcie_info#(TAG_WIDTH)::req_info req;

                req.lower_address  = cq_hdr.address[7-1:2];
                req.fbe            = cq_hdr.fbe;
                req.lbe            = cq_hdr.length != 1 ? cq_hdr.lbe : cq_hdr.fbe;
                req.rest_length    = cq_hdr.length;
                req.received_time = $time;
                info.request_register(cq_hdr.requester_id, cq_hdr.tag, req);
            end

            finish_item(cq_hdr);

            it++;
        end


//requester_remove(logic [16-1:0] requester_id)
    endtask
endclass


/////////////////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY REQUEST
class sequence_request_lib extends uvm_common::sequence_library#(config_sequence, uvm_pcie::header);
  `uvm_object_param_utils(uvm_pcie::sequence_request_lib)
  `uvm_sequence_library_utils(uvm_pcie::sequence_request_lib)

  function new(string name = "sequence_lib_tx");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(uvm_pcie::sequence_request::get_type());
    endfunction
endclass

