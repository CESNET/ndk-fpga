//-- sequence.sv
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// This low level sequence define bus functionality
function logic [sv_pcie_meta_pack::PCIE_META_REQ_HDR_W-1 : 0] gen_hdr(uvm_pcie_hdr::sequence_item cq_header_req, logic intel);
    automatic logic [sv_pcie_meta_pack::PCIE_META_REQ_HDR_W-1 : 0] ret = '0;

    if(intel) begin
        // Intel HDR:
        // DW count
        ret[10-1 : 0]   = cq_header_req.dw_count;
        // ADDR TYPE
        ret[12-1 : 10]  = cq_header_req.addr[2-1 : 0];
        // ATTR[1 : 0] - {No Snoop, Relax}
        ret[14-1 : 12] = cq_header_req.attr[1 : 0];
        // {EP, TD, TH, LN}
        ret[18-1 : 14] = '0;
        // ATTR[2] - ID-Based Ordering
        ret[19-1 : 18] = cq_header_req.attr[2];
        // TAG 8
        ret[20-1 : 19] = '0;
        // TC
        ret[23-1 : 20] = cq_header_req.tc;
        // TAG 9
        ret[24-1 : 23] = '0;
        // TYPE
        ret[32-1 : 24] = cq_header_req.req_type;
        // FBE
        ret[36-1 : 32] = cq_header_req.fbe;
        // LBE
        ret[40-1 : 36] = cq_header_req.lbe;
        // TAG
        ret[48-1 : 40] = cq_header_req.tag;
        // REQ ID
        ret[64-1 : 48] = cq_header_req.req_id;
        if (|cq_header_req.addr[64-1 : 32]) begin
            ret[128-1 : 64] = {cq_header_req.addr[32-1 : 2], cq_header_req.addr[2-1 : 0], cq_header_req.addr[64-1 : 32]};
        end else
            ret[128-1 : 64] = {32'h0000, cq_header_req.addr[2-1 : 0], cq_header_req.addr[32-1 : 2]};
    end else begin
        // ADDR TYPE
        ret[1 : 0]     = cq_header_req.addr[2-1 : 0];
        // ADDRESS
        ret[63 : 2]    = cq_header_req.addr[64-1 : 2];
        // DW count
        ret[74 : 64]   = cq_header_req.dw_count;
        // REQ TYPE
        ret[78 : 75]   = cq_header_req.req_type[4-1 : 0];
        // REQ ID
        ret[95 : 80]   = cq_header_req.req_id;
        // TAG (Solve tag generation for read requests)
        ret[103 : 96]  = cq_header_req.tag;
        // Target Function
        ret[111 : 104] = cq_header_req.t_func;
        // BAR ID, TODO: Use more BARs (Now one is used)
        ret[114 : 112] = cq_header_req.bar;
        // BAR Aperure
        ret[120 : 115] = cq_header_req.bar_ap;
        // TC
        ret[123 : 121] = cq_header_req.tc;
        // ATTR
        ret[126 : 124] = cq_header_req.attr;
        // FBE
    end
    return ret;
endfunction


function logic [sv_pcie_meta_pack::PCIE_CQ_META_WIDTH-sv_pcie_meta_pack::PCIE_META_REQ_HDR_W-1 : 0] gen_meta(uvm_pcie_hdr::sequence_item cq_header_req, logic intel);
    automatic logic [sv_pcie_meta_pack::PCIE_CQ_META_WIDTH-sv_pcie_meta_pack::PCIE_META_REQ_HDR_W-1 : 0] ret = '0;
    if(intel) begin
        ret[32-1 : 0]  = 6'd26;
        // BAR
        ret[35-1 : 32] = cq_header_req.bar;
    end else begin
        ret[39-1 : 35] = cq_header_req.fbe;
        // LBE
        ret[43-1 : 39] = cq_header_req.lbe;
        // TPH_PRESENT
        ret[44-1 : 43] = cq_header_req.tph_present;
        // TPH TYPE
        ret[46-1 : 44] = cq_header_req.tph_type;
        // TPH_ST_TAG
        ret[54-1 : 46] = cq_header_req.tph_st_tag;
    end
    return ret;
endfunction


class logic_vector_array_sequence#(ITEM_WIDTH, string DEVICE, string ENDPOINT_TYPE) extends uvm_sequence #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH));
    `uvm_object_param_utils(uvm_pcie_cq::logic_vector_array_sequence#(ITEM_WIDTH, DEVICE, ENDPOINT_TYPE))

    localparam IS_INTEL_DEV    = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");
    localparam IS_MFB_META_DEV = (ENDPOINT_TYPE == "P_TILE" || ENDPOINT_TYPE == "R_TILE") && IS_INTEL_DEV;
    mailbox#(uvm_pcie_hdr::sequence_item) tr_export;

    function new(string name = "logic_vector_array_sequence");
        super.new(name);
    endfunction

    task body;
        uvm_pcie_hdr::sequence_item cq_header_req;
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) m_pcie_data;
        uvm_pcie_hdr::msg_type rw;
        int unsigned tr_cnt;

        req = uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)::type_id::create("req");
        forever begin
            string msg = "";
            int unsigned data_size;

            tr_export.get(cq_header_req);
            start_item(req);

            rw = uvm_pcie_hdr::encode_type(cq_header_req.req_type, IS_INTEL_DEV);
            if (rw == uvm_pcie_hdr::TYPE_READ) begin
                logic [sv_pcie_meta_pack::PCIE_META_REQ_HDR_W-1 : 0] hdr;

                hdr = gen_hdr(cq_header_req, IS_INTEL_DEV);
                if (!IS_MFB_META_DEV) begin
                    req.data = new[sv_pcie_meta_pack::PCIE_META_REQ_HDR_W/ITEM_WIDTH];
                    req.data = {hdr[31 : 0], hdr[63 : 32], hdr[95 : 64], hdr[127 : 96]};
                end else begin
                    req.data = new[1];
                    req.data[0] = 'x;
                end
            end else begin
                m_pcie_data = uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)::type_id::create("m_pcie_data");
                assert(m_pcie_data.randomize() with {m_pcie_data.data.size() == cq_header_req.dw_count;});
                if (IS_MFB_META_DEV) begin
                    // In case of Intel
                    // Add only data to array
                    req.data = m_pcie_data.data;
                end else begin
                    // Add PCIe HDR and data to array
                   logic [sv_pcie_meta_pack::PCIE_META_REQ_HDR_W-1 : 0] hdr;

                   hdr = gen_hdr(cq_header_req, IS_INTEL_DEV);
                   if (ENDPOINT_TYPE == "H_TILE" && cq_header_req.req_type[5] == 1'b0) begin
                        req.data = new[m_pcie_data.data.size()+sv_pcie_meta_pack::PCIE_META_REQ_HDR_W/ITEM_WIDTH-1];
                        req.data = {hdr[31 : 0], hdr[63 : 32], hdr[95 : 64], m_pcie_data.data};
                    end else begin
                        req.data = new[m_pcie_data.data.size()+sv_pcie_meta_pack::PCIE_META_REQ_HDR_W/ITEM_WIDTH];
                        req.data = {hdr[31 : 0], hdr[63 : 32], hdr[95 : 64], hdr[127 : 96], m_pcie_data.data};
                    end
                end
            end

            tr_cnt++;

            msg = "\n\t =============== Driver CQ DATA =============== \n";
            msg = {msg, $sformatf("\nTransaction number: %0d\n",  tr_cnt)};
            msg = {msg, $sformatf("\nDriver CQ Response Data %s\n",  req.convert2string())};
            `uvm_info(this.get_full_name(), msg, UVM_FULL)

            finish_item(req);
        end
    endtask
endclass



class logic_vector_sequence#(META_WIDTH, string DEVICE, string ENDPOINT_TYPE) extends uvm_sequence #(uvm_logic_vector::sequence_item#(META_WIDTH));
    `uvm_object_param_utils(uvm_pcie_cq::logic_vector_sequence#(META_WIDTH, DEVICE, ENDPOINT_TYPE))

    localparam IS_INTEL_DEV    = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");
    localparam IS_MFB_META_DEV = (ENDPOINT_TYPE == "P_TILE" || ENDPOINT_TYPE == "R_TILE") && IS_INTEL_DEV;


    mailbox#(uvm_pcie_hdr::sequence_item) tr_export;
    protected int unsigned tr_cnt;

    function new(string name = "logic_vector_sequence");
        super.new(name);
        tr_cnt = 0;
    endfunction

    task body;

        forever begin
            uvm_pcie_hdr::sequence_item cq_header_req;

            tr_export.get(cq_header_req);

            tr_cnt++;
            req = uvm_logic_vector::sequence_item#(META_WIDTH)::type_id::create("req");

            start_item(req);

            req.data = '0;
            if (IS_MFB_META_DEV) begin
                // Add PCIe HDR to metadata
                req.data[sv_pcie_meta_pack::PCIE_META_REQ_HDR_W-1 : 0] = gen_hdr(cq_header_req, IS_INTEL_DEV);
            end
            req.data[sv_pcie_meta_pack::PCIE_CQ_META_WIDTH-1 : sv_pcie_meta_pack::PCIE_META_REQ_HDR_W] = gen_meta(cq_header_req, IS_INTEL_DEV);

            finish_item(req);
        end
    endtask
endclass

