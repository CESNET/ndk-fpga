//-- model.sv: Model of implementation
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class cc_mtc_item#(MFB_ITEM_WIDTH) extends uvm_common::sequence_item;

    uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) data_tr;
    logic [8-1 : 0]                                         tag;
    logic                                                   error;

    function string convert2string();
        string msg;

        msg = $sformatf( "\n\tDATA %s\n TAG %h\n ERROR %h", data_tr.convert2string(), tag, error);
        return msg;
    endfunction

endclass


virtual class model #(MFB_ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_mtc::model #(MFB_ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    //REQUEST (PCIE -> MI)
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH))                  analysis_imp_cq_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)) analysis_imp_cq_meta;
    uvm_analysis_port     #(uvm_mi::sequence_item_request #(MI_DATA_WIDTH, MI_ADDR_WIDTH, 0))        analysis_port_mi_data;

    //RESPONSE (MI -> PCIE)
    uvm_tlm_analysis_fifo #(uvm_mi::sequence_item_response #(MI_DATA_WIDTH))                         analysis_imp_cc_mi;
    uvm_analysis_port     #(uvm_logic_vector::sequence_item#(sv_pcie_meta_pack::PCIE_CC_META_WIDTH)) analysis_port_cc_meta;
    uvm_analysis_port     #(uvm_mtc::cc_mtc_item#(MFB_ITEM_WIDTH))                                   analysis_port_cc;

    protected int unsigned mi_tr_cnt;
    protected int unsigned pcie_cg_cnt;
    protected int unsigned pcie_cc_cnt;

    typedef struct {
        logic [4-1 : 0]      fbe;
        logic [4-1 : 0]      lbe;
        logic [MI_ADDR_WIDTH-1 : 0] addr;
        logic [3-1 : 0]      bar;
        uvm_pcie_hdr::msg_type tr_type;
        int unsigned         dw_cnt;
        int unsigned         tag;

        logic           tph_present;
        logic [2-1 : 0]  addr_type;
        //logic [3-1 : 0]  comp_st;
        logic [16-1 : 0] req_id;
        logic [8-1 : 0]  func_id;
        logic [3-1 : 0]  tc;
        logic [3-1 : 0]  attr;

        logic [8-1 : 0] tph_st_tag;
        logic [2-1 : 0] tph_type;
    } pcie_info;

    protected pcie_info request_rd[$];

    function new (string name, uvm_component parent = null);
        super.new(name, parent);
        analysis_imp_cq_data  = new("analysis_imp_cq_data" , this);
        analysis_imp_cq_meta  = new("analysis_imp_cq_meta" , this);
        analysis_port_mi_data = new("analysis_port_mi_data", this);

        analysis_imp_cc_mi    = new("analysis_imp_cc_mi", this);
        analysis_port_cc_meta = new("analysis_port_cc_meta", this);
        analysis_port_cc      = new("analysis_port_cc", this);

        mi_tr_cnt   = 0;
        pcie_cg_cnt = 0;
        mi_tr_cnt   = 0;
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (analysis_imp_cq_data.used() != 0);
        ret |= (analysis_imp_cq_meta.used() != 0);
        return ret;
    endfunction

    function uvm_mi::sequence_item_request #(MI_DATA_WIDTH, MI_ADDR_WIDTH, 0) gen_mi_read(input logic[32-1 : 0] addr, input logic[(32/8)-1 : 0] be);
        uvm_mi::sequence_item_request #(MI_DATA_WIDTH, MI_ADDR_WIDTH, 0) mi_tr;

        mi_tr = uvm_mi::sequence_item_request #(MI_DATA_WIDTH, MI_ADDR_WIDTH, 0)::type_id::create("mi_tr");
        mi_tr.dwr  = '0;
        mi_tr.addr = addr;
        mi_tr.be   = be;
        mi_tr.wr   = 1'b0;
        mi_tr.rd   = 1'b1;
        mi_tr.ardy = 1'b1;
        mi_tr.meta = 'z;
        return mi_tr;
    endfunction

    function uvm_mi::sequence_item_request #(MI_DATA_WIDTH, MI_ADDR_WIDTH, 0) gen_mi_write(input logic[32-1 : 0] addr, input logic[MFB_ITEM_WIDTH-1 : 0] data, input logic[(MI_DATA_WIDTH/8)-1 : 0] be);
        uvm_mi::sequence_item_request #(MI_DATA_WIDTH, MI_ADDR_WIDTH, 0) mi_tr;

        mi_tr = uvm_mi::sequence_item_request #(MI_DATA_WIDTH, MI_ADDR_WIDTH, 0)::type_id::create("mi_tr");
        mi_tr.dwr  = data;
        mi_tr.addr = addr;
        mi_tr.be   = be;
        mi_tr.wr   = 1'b1;
        mi_tr.rd   = 1'b0;
        mi_tr.ardy = 1'b1;
        mi_tr.meta = 'z;

        return mi_tr;
    endfunction

    pure virtual task get_pcie_request(output pcie_info info, logic [MFB_ITEM_WIDTH-1:0] data[]);

    task run_request();
        uvm_mi::sequence_item_request #(MI_DATA_WIDTH, MI_ADDR_WIDTH, 0)        mi_tr;

        logic [4-1 : 0]      fbe;
        logic [4-1 : 0]      lbe;
        logic [8-1 : 0]      req_type;
        logic [(MI_DATA_WIDTH/8)-1 : 0] be;

        logic[sv_pcie_meta_pack::PCIE_META_REQ_HDR_W-1 : 0] hdr;
        logic[(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH-sv_pcie_meta_pack::PCIE_META_REQ_HDR_W)-1 : 0] meta;

        forever begin
            pcie_info info;
            logic [MFB_ITEM_WIDTH-1:0] data[];

            get_pcie_request(info, data);

            if (info.tr_type == uvm_pcie_hdr::TYPE_WRITE || info.tr_type == uvm_pcie_hdr::TYPE_READ) begin
                logic  [MI_ADDR_WIDTH-1:0] mi_addr;

                case (info.bar)
                    3'b000  : mi_addr = 'h01000000;
                    3'b001  : mi_addr = 'h02000000;
                    3'b010  : mi_addr = 'h03000000;
                    3'b011  : mi_addr = 'h04000000;
                    3'b100  : mi_addr = 'h05000000;
                    3'b101  : mi_addr = 'h06000000;
                    3'b110  : mi_addr = 'h0A000000;
                    default : mi_addr = 'h0;
                endcase
                mi_addr += info.addr;

                for (int unsigned it = 0; it < info.dw_cnt; it++) begin
                    logic read;

                    if (it == 0) begin
                        be = info.fbe;
                    end else if (it == (info.dw_cnt - 1)) begin
                        be = info.lbe;
                    end else begin
                        be = '1;
                    end

                    if (info.tr_type == uvm_pcie_hdr::TYPE_WRITE) begin
                        mi_tr = gen_mi_write(mi_addr + it*4, data[it], be);
                        analysis_port_mi_data.write(mi_tr);
                    end else if (info.tr_type == uvm_pcie_hdr::TYPE_READ) begin
                        mi_tr = gen_mi_read(mi_addr + it*4, be);
                        analysis_port_mi_data.write(mi_tr);
                    end else begin
                        mi_tr = null;
                    end
                end
            end

            if (info.tr_type == uvm_pcie_hdr::TYPE_READ || info.tr_type == uvm_pcie_hdr::TYPE_ERR) begin
                request_rd.push_back(info);
            end
        end
    endtask

    pure virtual function void write_responses(pcie_info info,
                                          logic [7-1 : 0]  low_addr,
                                          logic [13-1 : 0] byte_cnt,
                                          logic [3-1 : 0]  comp_st,
                                          logic [8-1 : 0]  bus_num,
                                          logic [MFB_ITEM_WIDTH-1:0] data[]);

    task run_responses();
        logic [MFB_ITEM_WIDTH-1:0] data_fifo[$];

        forever begin
            logic [7-1 : 0]  low_addr;
            logic [13-1 : 0] byte_cnt;
            logic [3-1 : 0]  comp_st;
            logic [8-1 : 0]  tag;
            logic [8-1 : 0]  bus_num;

            uvm_mi::sequence_item_response #(MI_DATA_WIDTH) mi_cc_tr;
            pcie_info info;

            wait(request_rd.size() != 0);
            info = request_rd.pop_front();

            data_fifo = {};
            if (!(info.tr_type == uvm_pcie_hdr::TYPE_ERR)) begin
                for (int unsigned it = 0; it < info.dw_cnt; it++) begin
                    do begin
                        analysis_imp_cc_mi.get(mi_cc_tr);
                    end while(mi_cc_tr.drdy !== 1);
                    data_fifo.push_back(mi_cc_tr.drd);
                end
            end

            bus_num = 0;
            // Byte count computation
            if (info.dw_cnt == 1) begin
                casex (info.fbe)
                    4'b1xx1 : byte_cnt = 4;
                    4'b01x1 : byte_cnt = 3;
                    4'b1x10 : byte_cnt = 3;
                    4'b0011 : byte_cnt = 2;
                    4'b0110 : byte_cnt = 2;
                    4'b1100 : byte_cnt = 2;
                    4'b0001 : byte_cnt = 1;
                    4'b0010 : byte_cnt = 1;
                    4'b0100 : byte_cnt = 1;
                    4'b1000 : byte_cnt = 1;
                    4'b0000 : byte_cnt = 1;
                endcase
            end else begin
                //byte_cnt = unsigned'(info.dw_cnt * 4) - unsigned'(sv_dma_bus_pack::encode_fbe(info.fbe)) - unsigned'(sv_dma_bus_pack::encode_lbe(info.dw_cnt != 1 ? info.lbe : info.fbe));
                byte_cnt = unsigned'(info.dw_cnt * 4) - unsigned'(sv_dma_bus_pack::encode_fbe(info.fbe)) - unsigned'(sv_dma_bus_pack::encode_lbe(info.lbe));
            end

            if (info.tr_type == uvm_pcie_hdr::TYPE_ERR) begin
                // completion status (unsupported request)
                comp_st = 3'b001;
                low_addr = '0;
            end else begin
                comp_st = 3'b000;
                low_addr = {info.addr[7-1 : 2], sv_dma_bus_pack::encode_fbe(info.fbe)};
            end

            pcie_cc_cnt++;
            write_responses(info, low_addr, byte_cnt, comp_st, bus_num, data_fifo);
        end
    endtask


    task run_phase(uvm_phase phase);
        fork
            run_request();
            run_responses();
        join
    endtask
endclass


