// monitor.sv : Convert dma to mvb and mfb 
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class monitor extends uvm_monitor;
    `uvm_component_param_utils(uvm_dma::monitor);

    localparam ITEM_WIDTH = 32;

    uvm_analysis_port #(uvm_dma::sequence_item_rq) rq_analysis_port;
    uvm_analysis_port #(uvm_dma::sequence_item_rc) rc_analysis_port;

    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))                   rq_mfb;
    uvm_tlm_analysis_fifo#(uvm_logic_vector::sequence_item#(sv_dma_bus_pack::DMA_UPHDR_WIDTH))   rq_mvb;
    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))                   rc_mfb;
    uvm_tlm_analysis_fifo#(uvm_logic_vector::sequence_item#(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)) rc_mvb;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        rq_mfb = new("rq_mfb", this);
        rq_mvb = new("rq_mvb", this);
        rc_mfb = new("rc_mfb", this);
        rc_mvb = new("rc_mvb", this);

        rq_analysis_port = new("rq_analysis_port", this);
        rc_analysis_port = new("rc_analysis_port", this);
    endfunction
    
    task run_rq();
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)   tr_data;
        uvm_logic_vector::sequence_item#(sv_dma_bus_pack::DMA_UPHDR_WIDTH)  tr_meta;
        uvm_dma::sequence_item_rq tr_rq;

        forever begin
            rq_mvb.get(tr_meta);

            tr_rq = uvm_dma::sequence_item_rq::type_id::create("rq_item.item", this);

            tr_rq.hdr.relaxed     = tr_meta.data[sv_dma_bus_pack::DMA_REQUEST_W-1 : sv_dma_bus_pack::DMA_REQUEST_RELAXED_O];
            tr_rq.hdr.pasidvld    = tr_meta.data[sv_dma_bus_pack::DMA_REQUEST_PASIDVLD_O];
            tr_rq.hdr.pasid       = tr_meta.data[sv_dma_bus_pack::DMA_REQUEST_PASID_O];
            tr_rq.hdr.vfid        = tr_meta.data[sv_dma_bus_pack::DMA_REQUEST_PASID_O-1 : sv_dma_bus_pack::DMA_REQUEST_VFID_O];
            tr_rq.hdr.global_id   = tr_meta.data[sv_dma_bus_pack::DMA_REQUEST_VFID_O-1 : sv_dma_bus_pack::DMA_REQUEST_GLOBAL_O];
            tr_rq.hdr.unitid      = tr_meta.data[sv_dma_bus_pack::DMA_REQUEST_GLOBAL_O-1 : sv_dma_bus_pack::DMA_REQUEST_UNITID_O];
            tr_rq.hdr.tag         = tr_meta.data[sv_dma_bus_pack::DMA_REQUEST_UNITID_O-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_O];
            tr_rq.hdr.lastib      = tr_meta.data[sv_dma_bus_pack::DMA_REQUEST_TAG_O-1 : sv_dma_bus_pack::DMA_REQUEST_LASTIB_O];
            tr_rq.hdr.firstib     = tr_meta.data[sv_dma_bus_pack::DMA_REQUEST_LASTIB_O-1 : sv_dma_bus_pack::DMA_REQUEST_FIRSTIB_O];
            tr_rq.hdr.type_ide    = tr_meta.data[sv_dma_bus_pack::DMA_REQUEST_FIRSTIB_O-1 : sv_dma_bus_pack::DMA_REQUEST_TYPE_O];
            tr_rq.hdr.length      = tr_meta.data[sv_dma_bus_pack::DMA_REQUEST_TYPE_O-1 : sv_dma_bus_pack::DMA_REQUEST_LENGTH_O]; // Size in DWORDS

            if (tr_rq.hdr.type_ide == 1'b1) begin
                rq_mfb.get(tr_data);

                tr_rq.data = new[tr_data.data.size()](tr_data.data);

                if (tr_rq.data.size() != tr_rq.hdr.length) begin
                    string msg;
                     msg = $sformatf("\n\tDATA SIZE: %d META SIZE: %d (0x%h)", tr_rq.data.size(), tr_rq.hdr.length, tr_meta.data);
                    `uvm_fatal(this.get_full_name(), msg);
                end
            end else begin
                tr_rq.data = {};
            end

            rq_analysis_port.write(tr_rq);
        end
    endtask


    task run_rc();
        uvm_logic_vector::sequence_item#(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH) meta;
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)                   data;
        uvm_dma::sequence_item_rc dma_rc;
        forever begin
            logic [sv_dma_bus_pack::DMA_COMPLETION_LENGTH_W-1:0]    length;
            logic [sv_dma_bus_pack::DMA_COMPLETION_COMPLETED_W-1:0] completed;
            logic [sv_dma_bus_pack::DMA_COMPLETION_TAG_W-1:0]       tag;
            logic [sv_dma_bus_pack::DMA_COMPLETION_UNITID_W-1:0]    unit_id;


            rc_mvb.get(meta);
            rc_mfb.get(data);

            {unit_id, tag, completed, length} = meta.data; 
            dma_rc = uvm_dma::sequence_item_rc::type_id::create("dma_rc", this);
            dma_rc.length    = length; 
            dma_rc.completed = completed; 
            dma_rc.tag       = tag; 
            dma_rc.unit_id   = unit_id; 
            dma_rc.data      = data.data; 

            rc_analysis_port.write(dma_rc);
        end
    endtask

    task run_phase(uvm_phase phase);
        fork
            run_rq();
            run_rc();
        join
    endtask

endclass

