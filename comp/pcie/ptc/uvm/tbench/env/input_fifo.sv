//-- input_fifo.sv: Convert to input transactions
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša  <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class model_rc_input_fifo#(MEATA_WIDTH) extends uvm_common::fifo#(dma_header_rq);
    `uvm_component_param_utils(uvm_ptc::model_rc_input_fifo#(MEATA_WIDTH))

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(32))    mfb;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(MEATA_WIDTH)) mvb;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        mfb = new("mfb", this);
        mvb = new("mvb", this);
    endfunction

    virtual function void flush();
        super.flush();
        mfb.flush();
        mvb.flush();
    endfunction

    virtual function int unsigned used();
        return (super.used() || mfb.used() != 0 || mvb.used() != 0);
    endfunction


    task run_phase(uvm_phase phase);

        uvm_logic_vector_array::sequence_item#(32)    tr_mfb;
        uvm_logic_vector::sequence_item#(MEATA_WIDTH) tr_mvb;

        forever begin
            dma_header_rq tr;

            mvb.get(tr_mvb);

            tr = dma_header_rq::type_id::create("tr", this);
            tr.hdr = uvm_ptc_info::sequence_item::type_id::create("tr.hdr", this);

            tr.hdr.relaxed     = tr_mvb.data[sv_dma_bus_pack::DMA_REQUEST_W-1 : sv_dma_bus_pack::DMA_REQUEST_RELAXED_O];
            tr.hdr.pasidvld    = tr_mvb.data[sv_dma_bus_pack::DMA_REQUEST_PASIDVLD_O];
            tr.hdr.pasid       = tr_mvb.data[sv_dma_bus_pack::DMA_REQUEST_PASID_O];
            tr.hdr.vfid        = tr_mvb.data[sv_dma_bus_pack::DMA_REQUEST_PASID_O-1 : sv_dma_bus_pack::DMA_REQUEST_VFID_O];
            tr.hdr.global_id   = tr_mvb.data[sv_dma_bus_pack::DMA_REQUEST_VFID_O-1 : sv_dma_bus_pack::DMA_REQUEST_GLOBAL_O];
            tr.hdr.unitid      = tr_mvb.data[sv_dma_bus_pack::DMA_REQUEST_GLOBAL_O-1 : sv_dma_bus_pack::DMA_REQUEST_UNITID_O];
            tr.hdr.tag         = tr_mvb.data[sv_dma_bus_pack::DMA_REQUEST_UNITID_O-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_O];
            tr.hdr.lastib      = tr_mvb.data[sv_dma_bus_pack::DMA_REQUEST_TAG_O-1 : sv_dma_bus_pack::DMA_REQUEST_LASTIB_O];
            tr.hdr.firstib     = tr_mvb.data[sv_dma_bus_pack::DMA_REQUEST_LASTIB_O-1 : sv_dma_bus_pack::DMA_REQUEST_FIRSTIB_O];
            tr.hdr.type_ide    = tr_mvb.data[sv_dma_bus_pack::DMA_REQUEST_FIRSTIB_O-1 : sv_dma_bus_pack::DMA_REQUEST_TYPE_O];
            tr.hdr.length      = tr_mvb.data[sv_dma_bus_pack::DMA_REQUEST_TYPE_O-1 : sv_dma_bus_pack::DMA_REQUEST_LENGTH_O]; // Size in DWORDS

            if (tr.hdr.type_ide == 1'b1) begin
                string msg = "";

                mfb.get(tr_mfb);
                tr.data = tr_mfb.data;
                if (tr_mfb.data.size() != tr.hdr.length) begin
                    msg = {msg, $sformatf("\n\tDATA SIZE: %d META SIZE: %d",  tr_mfb.data.size(), tr.hdr.length)};
                    `uvm_fatal(this.get_full_name(), msg);
                end
            end else begin
                tr.data = {};
            end

            this.push_back(tr);
        end

    endtask
endclass


virtual class model_down_input_fifo#(PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH) extends uvm_common::fifo#(dma_header_rc);

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(32))           mfb_in;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(PCIE_DOWNHDR_WIDTH)) meta_in;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(PCIE_PREFIX_WIDTH))  prefix_in;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        mfb_in    = new("model_rc_mfb_in",        this);
        meta_in   = new("model_rc_meta_in",       this);
        prefix_in = new("model_rc_prefix_mvb_in", this);
    endfunction

    virtual function void flush();
        super.flush();
        mfb_in.flush();
        meta_in.flush();
        prefix_in.flush();
    endfunction

    virtual function int unsigned used();
        //return (super.used() || mfb_in.used() != 0 || meta_in.used() != 0 || prefix_in.used() != 0);
        return (super.used() || mfb_in.used() != 0);
    endfunction
endclass

class model_down_input_fifo_intel#(PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, DMA_PORTS) extends model_down_input_fifo#(PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH);
    `uvm_component_param_utils(uvm_ptc::model_down_input_fifo_intel#(PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, DMA_PORTS))

    localparam DMA_PORT_WIDTH = DMA_PORTS > 1 ? $clog2(DMA_PORTS) : 1;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_logic_vector_array::sequence_item #(32)           tr_data;
        uvm_logic_vector::sequence_item #(PCIE_DOWNHDR_WIDTH) tr_meta;

        forever begin
            dma_header_rc tr_out;

            mfb_in.get(tr_data);
            meta_in.get(tr_meta);

            tr_out = dma_header_rc::type_id::create("tr_out", this);
            tr_out.port = DMA_PORTS > 1 ? tr_meta.data[(PCIE_DOWNHDR_WIDTH-16)+DMA_PORT_WIDTH-1 : (PCIE_DOWNHDR_WIDTH-16)] : 0;
            tr_out.length    = tr_meta.data[10-1 :0];
            if (tr_meta.data[43 : 32] == 0)
                tr_out.completed = 1'b1;
            else
                tr_out.completed = 1'b0;
            tr_out.tag       = tr_meta.data[90-1 : 82];
            tr_out.unit_id   = 0;
            tr_out.data      = tr_data.data;

            this.push_back(tr_out);
        end
    endtask
endclass

class model_down_input_fifo_xilinx#(PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, DMA_PORTS) extends model_down_input_fifo#(PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH);
    `uvm_component_param_utils(uvm_ptc::model_down_input_fifo_xilinx#(PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, DMA_PORTS))

    localparam DMA_PORT_WIDTH = DMA_PORTS > 1 ? $clog2(DMA_PORTS) : 1;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_logic_vector_array::sequence_item #(32)           tr_data;

        forever begin
            logic [PCIE_DOWNHDR_WIDTH-1:0] meta;
            dma_header_rc tr_out;

            mfb_in.get(tr_data);

            for (int unsigned it = 0; it < (PCIE_DOWNHDR_WIDTH/32); it++) begin
                meta[((it+1)*32-1) -: 32] = tr_data.data[it];
            end

            tr_out = dma_header_rc::type_id::create("tr_out", this);
            tr_out.port = DMA_PORTS > 1 ? meta[48+DMA_PORT_WIDTH-1 : 48] : 0;
            tr_out.length    = meta[43-1 : 32];
            tr_out.completed = meta[30];
            tr_out.tag       = meta[72-1 : 64];
            tr_out.unit_id   = 0;
            tr_out.data = new[tr_data.data.size() - (PCIE_DOWNHDR_WIDTH/32)];
            for (int it = 0; it < tr_data.data.size() - (PCIE_DOWNHDR_WIDTH/32); it++) begin
                tr_out.data[it] = tr_data.data[it+(PCIE_DOWNHDR_WIDTH/32)];
            end
            this.push_back(tr_out);
        end
    endtask
endclass

