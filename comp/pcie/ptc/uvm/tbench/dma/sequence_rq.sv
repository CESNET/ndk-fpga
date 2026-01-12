// sequence_dma_rq.sv : sequence generating dma request.
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause
class config_sequence extends uvm_object;
    //NULL CLASS
    //

    virtual function string covnert2string();
        return "\nNULL CONFIGURATION";
    endfunction
endclass

class sequence_dma_rq#(
    int unsigned DMA_PORTS
) extends uvm_common::sequence_base#(config_sequence, uvm_dma::sequence_item_rq);
    `uvm_object_param_utils(uvm_dma::sequence_dma_rq#(DMA_PORTS))

    localparam MAX_REQUEST_SIZE = 128;
    localparam MAX_PAYLOAD_SIZE = 64;

    rand logic [sv_dma_bus_pack::DMA_REQUEST_UNITID_W-1:0] unit_id;
    rand int unsigned transactions;
    //protected logic [sv_dma_bus_pack::DMA_REQUEST_TAG_W-1:0] tags[logic [sv_dma_bus_pack::DMA_REQUEST_TAG_W-1:0]];
    uvm_dma::seq_info info;

    constraint trans_const {
        transactions inside {[20:60]};
        if (DMA_PORTS > 1) {
		    unit_id[($clog2(DMA_PORTS) > 1 ? $clog2(DMA_PORTS) : 1) -1:0] == 0;
	    }
    };

    function new(string name = "mi_cc_sequence");
        super.new(name);
        //tags.delete();
    endfunction

    task body;
        assert(uvm_config_db #(uvm_dma::seq_info)::get(m_sequencer, "", "info", info)) else begin
            `uvm_fatal(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get tag manager");
        end;
        info.requester_add(unit_id);

        req = uvm_dma::sequence_item_rq::type_id::create("req", m_sequencer);

        for (int unsigned it = 0; it < transactions; it++) begin
            wait(info.tags[unit_id].size() < (256/DMA_PORTS));
            //uvm_logic_vector::sequence_item #(1) hl_tr;
            start_item(req);

            assert(req.randomize() with {
                req.unitid == unit_id;
                (req.type_ide == 0) -> !(req.tag inside {info.tags[unit_id]});
                req.firstib inside {0};
                req.lastib  inside {0};
                req.length > 0;
                (req.type_ide == 1) -> req.length <= MAX_PAYLOAD_SIZE;
                (req.type_ide == 0) -> req.length <= MAX_REQUEST_SIZE;
            }) else begin
                `uvm_fatal(m_sequencer.get_full_name(), "\n\tsequence_dma_rq cannot randomize");
            end

            if (req.type_ide == 0) begin
                info.tag_add(unit_id, req.tag);
            end
            finish_item(req);
        end
    endtask
endclass

class sequence_dma_rq_lib #(
    int unsigned DMA_PORTS
) extends uvm_common::sequence_library#(config_sequence, uvm_dma::sequence_item_rq);
  `uvm_object_param_utils(uvm_dma::sequence_dma_rq_lib#(DMA_PORTS))
  `uvm_sequence_library_utils(uvm_dma::sequence_dma_rq_lib#(DMA_PORTS))

    function new(string name = "sequence_lib_rx");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(uvm_dma::sequence_dma_rq#(DMA_PORTS)::get_type());
    endfunction
endclass


