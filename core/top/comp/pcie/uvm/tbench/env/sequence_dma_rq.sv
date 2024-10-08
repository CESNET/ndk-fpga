// sequence_dma_rq.sv : sequence generating dma request.
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

// This low level sequence define bus functionality
class sequence_dma_rq#(DMA_PORTS) extends uvm_sequence#(uvm_dma::sequence_item_rq);
    `uvm_object_param_utils(uvm_pcie_top::sequence_dma_rq#(DMA_PORTS))

    localparam MAX_REQUEST_SIZE = 128;
    localparam MAX_PAYLOAD_SIZE = 64;

    rand int unsigned unit_id;
    rand int unsigned transactions;
    //protected logic [sv_dma_bus_pack::DMA_REQUEST_TAG_W-1:0] tags[logic [sv_dma_bus_pack::DMA_REQUEST_TAG_W-1:0]];
    uvm_dma::seq_info info;

    constraint trans_const {
        transactions inside {[20:60]};
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
                req.hdr.unitid == unit_id;
                if (DMA_PORTS > 1) {
                    req.hdr.tag[sv_dma_bus_pack::DMA_REQUEST_TAG_W-1 -: $clog2(DMA_PORTS) > 1 ? $clog2(DMA_PORTS) : 1] == unit_id[($clog2(DMA_PORTS) > 1 ? $clog2(DMA_PORTS) : 1) -1:0];
                }
                (req.hdr.type_ide == 0) -> !(req.hdr.tag inside {info.tags[unit_id]});
                req.hdr.firstib inside {0};
                req.hdr.lastib  inside {0};
                req.hdr.length > 0;
                (req.hdr.type_ide == 1) -> req.hdr.length <= MAX_PAYLOAD_SIZE; 
                (req.hdr.type_ide == 0) -> req.hdr.length <= MAX_REQUEST_SIZE; 
            }) else begin
                `uvm_fatal(m_sequencer.get_full_name(), "\n\tsequence_dma_rq cannot randomize");
            end

            if (req.hdr.type_ide == 0) begin
                info.tag_add(unit_id, req.hdr.tag);
            end
            finish_item(req);
        end
    endtask
endclass
