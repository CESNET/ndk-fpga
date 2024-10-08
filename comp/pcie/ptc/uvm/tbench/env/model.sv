//-- model.sv: Model of implementation
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž  <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

virtual class model_rc #(DMA_PORTS, PCIE_UPHDR_WIDTH) extends uvm_component;
    //`uvm_component_param_utils(uvm_ptc::model_rc#(DMA_PORTS, PCIE_UPHDR_WIDTH))

    // Model inputs
    uvm_common::fifo#(dma_header_rq) model_up[DMA_PORTS];

    // Model outputs
    uvm_analysis_port #(pcie_data#(PCIE_UPHDR_WIDTH))  model_down;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        for (int unsigned it = 0; it < DMA_PORTS; it++) begin
            string str_it;

            str_it.itoa(it);
            model_up[it] = null;
        end
        model_down = new("model_down", this);
    endfunction

    typedef struct packed {
        logic [sv_dma_bus_pack::DMA_REQUEST_GLOBAL_W-1 : 0]    global_id;
        // Padding                            "00"
        logic [2-1 : 0]                       padd_1;
        logic [(sv_dma_bus_pack::DMA_REQUEST_TAG_W + 8)-1 : 0] req_id; // requester ID |vfid|"00000000"(MSB)|
        logic [sv_dma_bus_pack::DMA_REQUEST_TAG_W-1 : 0]       tag; // tag
        logic [4-1 : 0]                       lastbe; // last byte enable
        logic [4-1 : 0]                       firstbe; // first byte enable
        logic [3-1 : 0]                       fmt; // Request type |0|read_write|hdr_type ('1' for 4DWORD '0' for 3DWORD)
        logic [5-1 : 0]                       type_n;
        logic [1-1 : 0]                       tag_9;

        logic [3-1 : 0]                       tc; // Traffic Class
        logic [1-1 : 0]                       tag_8;
        // Padding                            "0000"
        logic [3-1 : 0]                       padd_0;
        logic [1-1 : 0]                       td; // ECRC
        logic [1-1 : 0]                       ep; // Poisoned request
        logic [sv_dma_bus_pack::DMA_REQUEST_RELAXED_W-1 : 0]   relaxed; // Relaxed bit
        logic [1-1 : 0]                       snoop; // Snoop bit
        logic [2-1 : 0]                       at;
        logic [10-1 : 0]                      len; // LSB (Paket size in DWORD)
    } pcie_header_rq;

    virtual function pcie_data#(PCIE_UPHDR_WIDTH) create_data(pcie_header_rq pcie_header_out,  dma_header_rq header_rq);
        `uvm_fatal(this.get_full_name(), "\n\tThis function is not implemented");
    endfunction

    task parse(int index);

        logic [4-1 : 0] fbe;
        logic [4-1 : 0] lbe;
        logic [8-1 : 0] be;
        logic [1-1 : 0] hdr_type;
        // DMA HEADER
        dma_header_rq header_rq;
        // PCIE HEADER
        pcie_header_rq pcie_header_out;

        model_up[index].get(header_rq);

        fbe = sv_dma_bus_pack::decode_fbe(header_rq.hdr.firstib);
        lbe = sv_dma_bus_pack::decode_lbe(header_rq.hdr.lastib);
        if (header_rq.hdr.length == 0)
            be = '0;
        else if (header_rq.hdr.length == 1)
            be = {4'h0, (fbe & lbe)};
        else
            be = {lbe, fbe};

        pcie_header_out.len     = header_rq.hdr.length[10-1 : 0];
        pcie_header_out.at      = '0;
        pcie_header_out.relaxed = header_rq.hdr.relaxed;
        // no snoop
        pcie_header_out.snoop  = '0;
        // EP
        pcie_header_out.ep     = '0;
        // TD
        pcie_header_out.td     = '0;
        // Padding "000"
        pcie_header_out.padd_0 = '0;
        pcie_header_out.tag_8  = (sv_dma_bus_pack::DMA_COMPLETION_TAG_W == 9);
        // TC
        pcie_header_out.tc    = '0;
        pcie_header_out.tag_9 = (sv_dma_bus_pack::DMA_COMPLETION_TAG_W == 10);
        // TYPE
        pcie_header_out.type_n = '0;
        // Upravit pro 3DW (vrchnich 32 bitu global id jsou 0) hlavičku (tam bude posledni bit 0)
        // Navodit takovy stav
        if (|header_rq.hdr.global_id[64-1 : 32]) begin
            pcie_header_out.fmt = {1'b0, header_rq.hdr.type_ide, 1'b1};
        end else
            pcie_header_out.fmt = {1'b0, header_rq.hdr.type_ide, 1'b0};

        pcie_header_out.firstbe = be[4-1 : 0];
        pcie_header_out.lastbe  = be[8-1 : 4];

        if (header_rq.hdr.type_ide == 1'b0) begin
            pcie_header_out.tag = header_rq.hdr.tag;
        end else
            pcie_header_out.tag = '0;

        pcie_header_out.req_id = {8'h00, header_rq.hdr.vfid};
        pcie_header_out.padd_1 = '0;

        if (|header_rq.hdr.global_id[64-1 : 32]) begin
            pcie_header_out.global_id = {header_rq.hdr.global_id[32-1 : 2], pcie_header_out.padd_1, header_rq.hdr.global_id[64-1 : 32]};
        end else begin
            pcie_header_out.global_id = {header_rq.hdr.global_id[32-1 : 2], pcie_header_out.padd_1, 32'h0000};
        end

        model_down.write(create_data(pcie_header_out, header_rq));
    endtask

    task run_phase(uvm_phase phase);
        for (int i = 0; i < DMA_PORTS; i++) begin
            fork
                automatic int unsigned index = i;
                forever begin
                    parse(index);
                end
            join_none;
        end
    endtask
endclass

class model_rc_intel #(DMA_PORTS, PCIE_UPHDR_WIDTH, TYLE) extends model_rc #(DMA_PORTS, PCIE_UPHDR_WIDTH);
    `uvm_component_param_utils(uvm_ptc::model_rc_intel#(DMA_PORTS, PCIE_UPHDR_WIDTH, TYLE))

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function pcie_data#(PCIE_UPHDR_WIDTH) create_data(pcie_header_rq pcie_header_out,  dma_header_rq header_rq);
        pcie_data#(PCIE_UPHDR_WIDTH) ret;

        ret = pcie_data#(PCIE_UPHDR_WIDTH)::type_id::create("ret", this);
        ret.meta = {pcie_header_out.global_id, pcie_header_out.req_id, pcie_header_out.tag,
                    pcie_header_out.lastbe, pcie_header_out.firstbe, pcie_header_out.fmt, pcie_header_out.type_n,
                    pcie_header_out.tag_9, pcie_header_out.tc, pcie_header_out.tag_8, pcie_header_out.padd_0,
                    pcie_header_out.td, pcie_header_out.ep, pcie_header_out.relaxed, pcie_header_out.snoop,
                    pcie_header_out.at, pcie_header_out.len};

        if (header_rq.data.size() != 0) begin
            if (TYLE == "H_TILE") begin
                if (header_rq.hdr.type_ide == 1'b1) begin
                    ret.data = new[header_rq.data.size() + 4];
                end else
                    ret.data = new[4];

                ret.data[0 : 4-1] = {<<32{ret.meta}};

                if (header_rq.hdr.type_ide == 1'b1) begin
                    for (int j = 0; j < header_rq.data.size; j++) begin
                        ret.data[j+4] = header_rq.data[j];
                    end
                end
            end else begin
                ret.data = new[header_rq.data.size()];

                for (int j = 0; j < header_rq.data.size(); j++) begin
                    ret.data[j] = header_rq.data[j];
                end
            end
        end else begin
            ret.data    = new[1];
            ret.data[0] = 32'h12345678;
        end

        return ret;
    endfunction
endclass

class model_rc_xilinx #(DMA_PORTS, PCIE_UPHDR_WIDTH) extends model_rc #(DMA_PORTS, PCIE_UPHDR_WIDTH);
    `uvm_component_param_utils(uvm_ptc::model_rc_xilinx#(DMA_PORTS, PCIE_UPHDR_WIDTH))

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function pcie_data#(PCIE_UPHDR_WIDTH) create_data(pcie_header_rq pcie_header_out,  dma_header_rq header_rq);
        pcie_data#(PCIE_UPHDR_WIDTH) ret;

        ret = pcie_data#(PCIE_UPHDR_WIDTH)::type_id::create("ret", this);
        ret.meta = {1'b0, pcie_header_out.relaxed, 21'b000000000000000000000, pcie_header_out.tag,
                       pcie_header_out.req_id, 1'b0, 3'b000, header_rq.hdr.type_ide, header_rq.hdr.length,
                       header_rq.hdr.global_id[63 : 2], 2'b00};
        // padding    [end : 126] ('0)
        // TAG        [103 : 96]
        // REQUEST ID [95 : 80]
        // padding    [79 : 79]
        // TYPE       [78 : 75]
        // SIZE       [74 : 64]
        // ADDRESS    [63 : 2]
        // padding    [1 : 0]

        if (header_rq.data.size() != 0) begin
            if (header_rq.hdr.type_ide == 1'b1) begin
                ret.data = new[header_rq.data.size() + 4];
            end else
                ret.data = new[4];

            ret.data[0 : 4-1] = {<<32{ret.meta}};

            if (header_rq.hdr.type_ide == 1'b1) begin
                for (int j = 0; j < header_rq.data.size; j++) begin
                    ret.data[j+4] = header_rq.data[j];
                end
            end
        end else begin
            ret.data    = new[1];
            ret.data[0] = 32'h12345678;
        end


        return ret;
    endfunction
endclass


class down_model #(DMA_PORTS) extends uvm_component;
    `uvm_component_param_utils(uvm_ptc::down_model#(DMA_PORTS))

    localparam PORTS_W_FIX = (DMA_PORTS > 1) ? $clog2(DMA_PORTS) : 1;

    // Model inputs
    uvm_common::fifo#(dma_header_rc) model_rc;

    uvm_analysis_port #(pcie_data#(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH))  model_down[DMA_PORTS];

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);
        model_rc = null;

        for (int unsigned it = 0; it < DMA_PORTS; it++) begin
            string str_it;

            str_it.itoa(it);
            model_down[it] = new({"model_down_", str_it}, this);
        end
    endfunction

    task run_phase(uvm_phase phase);
        dma_header_rc           tr_rc;
        pcie_data#(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH) tr_out;

        if (model_rc == null) begin
            `uvm_fatal(this.get_full_name(), "\n\t input port model_rc is null");
        end

        forever begin
            string debug_msg = "";

            model_rc.get(tr_rc);

            tr_out = pcie_data#(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)::type_id::create("tr_out", this);

            tr_out.data = tr_rc.data;
            tr_out.meta[11-1:0]  = tr_rc.length;
            tr_out.meta[12-1]    = tr_rc.completed;
            tr_out.meta[20-1:12] = tr_rc.tag;
            tr_out.meta[28-1:20] = tr_rc.unit_id;

            if (tr_rc.port < DMA_PORTS) begin
                model_down[tr_rc.port].write(tr_out);
            end else begin
                `uvm_error(this.get_full_name(), $sformatf("\n\tPort %0d is out of range [0:%0d]", tr_rc.port, DMA_PORTS));
            end

            debug_msg = {debug_msg, $sformatf("\n\t ================ DOWN MODEL =============== \n")};
            if (this.get_report_verbosity_level() >= UVM_FULL) begin
                debug_msg = {debug_msg, $sformatf("\t PORT:                %0d\n",  tr_rc.port)};
                debug_msg = {debug_msg, $sformatf("\t LENGTH:              %0d\n",  tr_rc.length)};
                debug_msg = {debug_msg, $sformatf("\t COMPLETED:           %0d\n",  tr_rc.completed)};
                debug_msg = {debug_msg, $sformatf("\t TAG:                 %0d\n",  tr_rc.tag)};
                debug_msg = {debug_msg, $sformatf("\t UNIT ID:             %0d\n",  tr_rc.unit_id)};
                debug_msg = {debug_msg, $sformatf("\t DATA:                %p\n",  tr_rc.data)};
            end

            debug_msg = {debug_msg, $sformatf("\t DOWN MODEL META IN:  %h\n",  tr_out.meta)};
            debug_msg = {debug_msg, $sformatf("\t DOWN MODEL MFB IN:   %p\n",  tr_out.data)};
            `uvm_info(this.get_full_name(), debug_msg ,UVM_HIGH);

        end
    endtask
endclass
