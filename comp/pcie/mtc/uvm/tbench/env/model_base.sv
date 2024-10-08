//-- model.sv: Model of implementation
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class model_base #(MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends model #(MFB_ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_component_param_utils(uvm_mtc::model_base #(MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    localparam IS_INTEL_DEV    = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");
    localparam IS_XILINX_DEV   = (DEVICE == "ULTRASCALE" || DEVICE == "7SERIES");
    localparam IS_MFB_META_DEV = (ENDPOINT_TYPE == "P_TILE" || ENDPOINT_TYPE == "R_TILE") && IS_INTEL_DEV;


    function new (string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task get_pcie_request(output pcie_info info, logic [MFB_ITEM_WIDTH-1:0] data[]);
        logic[sv_pcie_meta_pack::PCIE_META_REQ_HDR_W-1 : 0] hdr;
        uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH)                  cq_data_tr;
        uvm_logic_vector::sequence_item#(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH) cq_meta_tr;

        logic [64-1 : 0] addr;
        logic [6-1 : 0] bar_ap = 6'd26;
        logic [64-1 : 0] tlp_addr_mask = '0;
        logic[(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH-sv_pcie_meta_pack::PCIE_META_REQ_HDR_W)-1 : 0] meta;
        int unsigned hdr_offset = 0;

        analysis_imp_cq_meta.get(cq_meta_tr);
        meta = cq_meta_tr.data[sv_pcie_meta_pack::PCIE_CQ_META_WIDTH-1 : sv_pcie_meta_pack::PCIE_META_REQ_HDR_W];

        `uvm_info(this.get_full_name(), cq_meta_tr.convert2string() ,UVM_MEDIUM)

        if (IS_MFB_META_DEV) begin
            // Only Intel
            hdr      = cq_meta_tr.data[sv_pcie_meta_pack::PCIE_META_REQ_HDR_W-1 : 0];
            info.fbe      = hdr[36-1 : 32];
            info.lbe      = hdr[40-1 : 36];
            info.dw_cnt   = hdr[10-1 : 0];
            info.tr_type = uvm_pcie_hdr::encode_type(hdr[32-1 : 24], IS_INTEL_DEV);

            analysis_imp_cq_data.get(cq_data_tr);
            data = cq_data_tr.data;
        end else begin
            if (IS_INTEL_DEV) begin
                analysis_imp_cq_data.get(cq_data_tr);
                `uvm_info(this.get_full_name(), cq_data_tr.convert2string() ,UVM_MEDIUM)
                // GET HEADER
                for (int unsigned it = 0; it < (sv_pcie_meta_pack::PCIE_META_REQ_HDR_W/MFB_ITEM_WIDTH); it++) begin
                    hdr[((it+1)*32-1) -: 32] = cq_data_tr.data[it];
                end

                info.fbe        = hdr[36-1 : 32];
                info.lbe        = hdr[40-1 : 36];
                info.dw_cnt     = hdr[10-1 : 0];
                info.tr_type = uvm_pcie_hdr::encode_type(hdr[32-1 : 24], IS_INTEL_DEV);
            end else begin
                analysis_imp_cq_data.get(cq_data_tr);
                `uvm_info(this.get_full_name(), cq_data_tr.convert2string() ,UVM_MEDIUM)
                // GET HEADER
                for (int unsigned it = 0; it < (sv_pcie_meta_pack::PCIE_META_REQ_HDR_W/MFB_ITEM_WIDTH); it++) begin
                    hdr[((it+1)*32-1) -: 32] = cq_data_tr.data[it];
                end

                info.dw_cnt            = hdr[75-1 : 64];
                info.fbe               = meta[39-1 : 35];
                info.lbe               = meta[43-1 : 39];
                info.tr_type = uvm_pcie_hdr::encode_type(hdr[79-1 : 75], IS_INTEL_DEV);
            end
        end

        if (DEVICE == "ULTRASCALE" || DEVICE == "7SERIES") begin
            hdr_offset = sv_pcie_meta_pack::PCIE_META_REQ_HDR_W/MFB_ITEM_WIDTH;
        end else if(DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
            if (hdr[29] == 1'b1) begin
                if (ENDPOINT_TYPE == "H_TILE")
                    hdr_offset = sv_pcie_meta_pack::PCIE_META_REQ_HDR_W/MFB_ITEM_WIDTH;
            end else begin
                if (ENDPOINT_TYPE == "H_TILE")
                    hdr_offset = sv_pcie_meta_pack::PCIE_META_REQ_HDR_W/MFB_ITEM_WIDTH-1;
            end
        end

        data = new[cq_data_tr.data.size()-hdr_offset];
        for (int unsigned it = 0; it < (cq_data_tr.data.size() - hdr_offset); it++) begin
           data[it] = cq_data_tr.data[hdr_offset + it];
        end


        if (DEVICE == "ULTRASCALE" || DEVICE == "7SERIES") begin
            addr   = hdr[64-1 : 0];
            info.bar    = hdr[115-1 : 112];
            bar_ap = hdr[121-1 : 115];
        end else if(DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
            if (hdr[29] == 1'b1) begin
                addr = {hdr[95 : 64], hdr[127 : 98], 2'b00};
            end else begin
                addr = {32'h0, hdr[95 : 66], 2'b00};
            end

            info.bar  = meta[35-1 : 32];
        end

        for (int unsigned it = 0; it < bar_ap; it++) begin
            tlp_addr_mask[it] = 1'b1;
        end

        info.addr = (addr & tlp_addr_mask);


        if (IS_INTEL_DEV) begin
            // Low address computation
            info.addr_type = hdr[12-1 : 10];
            info.dw_cnt    = hdr[10-1 : 0];
            info.req_id         = hdr[64-1 : 48];
            info.tag            = hdr[48-1 : 40];
            info.func_id        = meta[8-1 : 0];
            info.tc             = hdr[23-1 : 20];
            info.attr[2-1 : 0]  = hdr[14-1 : 12];
            info.attr[2]        = hdr[19-1 : 18];
        end else begin
            // Low address computation
            info.addr_type         = hdr[2-1 : 0];
            info.dw_cnt            = hdr[75-1 : 64];
            info.req_id            = hdr[96-1 : 80];
            info.tag               = hdr[104-1 : 96];
            info.func_id           = hdr[112-1 : 104];
            info.tc                = hdr[124-1 : 121];
            info.attr              = hdr[127-1 : 124];
            info.tph_st_tag  = meta[54-1 : 46];
            info.tph_type    = meta[46-1 : 44];
            info.tph_present = meta[44-1 : 43];
        end

        if (info.dw_cnt == 0) begin
            info.dw_cnt = 1024;
        end
    endtask

    virtual function void write_responses(pcie_info info,
                                          logic [7-1 : 0]  low_addr,
                                          logic [13-1 : 0] byte_cnt,
                                          logic [3-1 : 0]  comp_st,
                                          logic [8-1 : 0]  bus_num,
                                          logic [MFB_ITEM_WIDTH-1:0] data[]);


        localparam IS_INTEL_DEV    = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");
        localparam IS_XILINX_DEV   = (DEVICE == "ULTRASCALE" || DEVICE == "7SERIES");
        localparam IS_MFB_META_DEV = (ENDPOINT_TYPE == "P_TILE" || ENDPOINT_TYPE == "R_TILE") && IS_INTEL_DEV;

        logic [8-1 : 0]  tag;
        logic [11-1:0]   dw_cnt;
        logic[sv_pcie_meta_pack::PCIE_META_CPL_HDR_W-1 : 0]                                       hdr  = '0;
        logic[sv_pcie_meta_pack::PCIE_CC_META_WIDTH-sv_pcie_meta_pack::PCIE_META_CPL_HDR_W-1 : 0] meta = '0;

        uvm_mtc::cc_mtc_item#(MFB_ITEM_WIDTH)                                   cc_tr;
        uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH)                  cc_data_tr;
        uvm_logic_vector::sequence_item#(sv_pcie_meta_pack::PCIE_CC_META_WIDTH) cc_meta_tr;

        cc_tr           = new();

        cc_data_tr = uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)::type_id::create("cc_data_tr_item");
        cc_meta_tr = uvm_logic_vector::sequence_item #(sv_pcie_meta_pack::PCIE_CC_META_WIDTH)::type_id::create("cc_meta_tr_item");
        cc_meta_tr.data = '0;

        tag = info.tag;
        if (IS_INTEL_DEV) begin
            dw_cnt = (info.tr_type != uvm_pcie_hdr::TYPE_ERR) ? info.dw_cnt : 1;
            hdr = {info.req_id, tag, 1'b0, low_addr, 16'h0, comp_st, 1'b0, byte_cnt[12-1 : 0], 8'b01001010, 1'b0, info.tc, 1'b0, info.attr[2], 4'b0000, info.attr[2-1 : 0], info.addr_type, dw_cnt[10-1 : 0]};
        end else begin
            dw_cnt = (info.tr_type != uvm_pcie_hdr::TYPE_ERR) ? info.dw_cnt : 0;
            hdr = {1'b0, info.attr, info.tc, 1'b0, bus_num, info.func_id, tag , info.req_id, 1'b0, 1'b0, comp_st, dw_cnt, 2'b00, 1'b0, byte_cnt, 6'b000000, info.addr_type, 1'b0, low_addr};
            meta = {8'b00000000, info.tph_st_tag, 5'b00000, info.tph_type, info.tph_present, info.lbe, info.fbe};
        end

        cc_meta_tr.data[sv_pcie_meta_pack::PCIE_META_CPL_HDR_W-1 : 0] = hdr;
        if (!IS_MFB_META_DEV) begin
            if ((info.tr_type == uvm_pcie_hdr::TYPE_ERR) && IS_XILINX_DEV) begin
                cc_data_tr.data = {hdr[1*32-1 : 0*32], hdr[2*32-1 : 1*32], hdr[3*32-1 : 2*32], meta[1*32-1 : 0*32], 32'h0, 32'h0, 32'h0, 32'h0, data};
            end else begin
                cc_data_tr.data = {hdr[1*32-1 : 0*32], hdr[2*32-1 : 1*32], hdr[3*32-1 : 2*32], data};
            end
        end else begin
            if ((info.tr_type == uvm_pcie_hdr::TYPE_ERR)) begin
                cc_data_tr.data = {32'h0, data};
                cc_meta_tr.data[sv_pcie_meta_pack::PCIE_CC_META_WIDTH-1 : sv_pcie_meta_pack::PCIE_META_CPL_HDR_W] = meta;
            end else begin
                cc_data_tr.data = data;
            end
        end

        cc_tr.data_tr = cc_data_tr;
        cc_tr.tag     = info.tag;
        cc_tr.error   = (info.tr_type == uvm_pcie_hdr::TYPE_ERR);
        analysis_port_cc.write(cc_tr);
        analysis_port_cc_meta.write(cc_meta_tr);
    endfunction
endclass

