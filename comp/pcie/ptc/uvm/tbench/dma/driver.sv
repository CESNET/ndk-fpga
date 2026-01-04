// driver.sv:
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class driver extends uvm_driver#(uvm_dma::sequence_item_rq);
    `uvm_component_param_utils(uvm_dma::driver);

    localparam DMA_UPHDR_WIDTH_W = sv_dma_bus_pack::DMA_UPHDR_WIDTH;
    //SEND DATA
    protected uvm_common::fifo#(uvm_logic_vector_array::sequence_item#(32))          fifo_rq_mfb_data;
    protected uvm_common::fifo#(uvm_logic_vector::sequence_item#(DMA_UPHDR_WIDTH_W)) fifo_rq_mvb;


    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        //fifo_rq_mfb_data = uvm_common::fifo#(uvm_logic_vector_array::sequence_item#(32))         ::type_id::create("fifo_rq_mfb_data", this);
        //fifo_rq_mvb      = uvm_common::fifo#(uvm_logic_vector::sequence_item#(DMA_UPHDR_WIDTH_W))::type_id::create("fifo_rq_mvb", this);
    endfunction

    task run_phase(uvm_phase phase);

        assert(uvm_config_db #(uvm_common::fifo#(uvm_logic_vector_array::sequence_item#(32)))
            ::get(this, "", "fifo_rq_mfb_data", fifo_rq_mfb_data)) else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot get mfb data");
        end
        assert(uvm_config_db #(uvm_common::fifo#(uvm_logic_vector::sequence_item#(DMA_UPHDR_WIDTH_W)))
            ::get(this, "", "fifo_rq_mvb", fifo_rq_mvb)) else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot get mvb fifo");
        end


        forever begin
            //logic [sv_dma_bus_pack::DMA_REQUEST_LENGTH_W-1 : 0]  packet_size;
            uvm_logic_vector_array::sequence_item#(32)  dma_data;
            uvm_logic_vector::sequence_item#(DMA_UPHDR_WIDTH_W) dma_hdr;

            wait (fifo_rq_mfb_data.size() == 0  || fifo_rq_mvb.size() == 0);
            wait (fifo_rq_mfb_data.size() <  20 && fifo_rq_mvb.size() <  20);
            seq_item_port.get_next_item(req);

            dma_data = uvm_logic_vector_array::sequence_item#(32)::type_id::create("dma_data", this);
            dma_hdr  = uvm_logic_vector::sequence_item#(DMA_UPHDR_WIDTH_W)::type_id::create("dma_hdr", this);

            dma_data.data = new[req.data.size()](req.data);
            dma_hdr.data = {req.relaxed, req.pasidvld, req.pasid, req.vfid, req.global_id,
                            req.unitid, req.tag, req.lastib, req.firstib, req.type_ide,
                            req.length};

            if (req.type_ide == 1) begin
                fifo_rq_mfb_data.push_back(dma_data);
            end
            fifo_rq_mvb     .push_back(dma_hdr);

            seq_item_port.item_done();
        end
    endtask

endclass


