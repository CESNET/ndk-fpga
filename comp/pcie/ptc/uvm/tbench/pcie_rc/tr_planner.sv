//-- tr_planner.sv: Transaction planner
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

let min(a,b) = (a < b) ? a : b;

class tr_planner #(ITEM_WIDTH, RQ_TUSER_WIDTH, PCIE_DOWNHDR_WIDTH, RCB_SIZE, CLK_PERIOD, string DEVICE) extends uvm_component;
    `uvm_component_param_utils(uvm_pcie_rc::tr_planner #(ITEM_WIDTH, RQ_TUSER_WIDTH, PCIE_DOWNHDR_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE))

    localparam LOW_ADDR_WIDTH = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? 7 : 12; // 7 for INTEL 12 XILINX
    localparam BYTE_CNT_WIDTH = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? 12 : 13; // 12 for INTEL 13 XILINX
    localparam LEN_WIDTH      = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? 10 : 11; // 10 for INTEL 11 XILINX
    localparam RCB            = (RCB_SIZE == 1'b0) ? 64 : 128; // 64 for '0' 128 for '1'

    uvm_analysis_imp#(uvm_logic_vector::sequence_item#(ITEM_WIDTH), tr_planner #(ITEM_WIDTH, RQ_TUSER_WIDTH, PCIE_DOWNHDR_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE)) analysis_imp;
    uvm_logic_vector::sequence_item #(PCIE_DOWNHDR_WIDTH) logic_array[$];
    uvm_logic_vector_array::sequence_item #(32)           byte_array[$];
    uvm_logic_vector::sequence_item#(ITEM_WIDTH)          headers[$];
    int unsigned mvb_cnt = 0;
    int unsigned mfb_cnt = 0;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        analysis_imp = new("analysis_imp", this);
    endfunction

    typedef struct{
        uvm_logic_vector_array::sequence_item#(32) data;
        uvm_ptc_info_rc::sequence_item #(DEVICE)   hdr;
    } pcie_info;

    task split (uvm_ptc_info_rc::sequence_item #(DEVICE) pcie_tr);
        uvm_logic_vector_array::sequence_item#(32) pcie_data;
        int unsigned                 rcbs;
        int unsigned                 index;
        int unsigned                 l;
        int unsigned                 length;
        int unsigned                 lbe;
        logic [LEN_WIDTH-1 : 0]      comp_length;
        logic [BYTE_CNT_WIDTH-1 : 0] byte_count;
        logic [16-1 : 0]             completer_id = '0; // '0
        logic [3-1 : 0]              complete_st  = '0; // Completition Status
        logic bcm                                 = 1'b0;
        logic completed                           = 1'b0;
        logic [LOW_ADDR_WIDTH-1 : 0] address;
        uvm_logic_vector::sequence_item#(PCIE_DOWNHDR_WIDTH) comp_hdr;
        uvm_logic_vector_array::sequence_item#(32)           comp_data;
        string debug_msg = "\n";

        lbe     = int'(sv_dma_bus_pack::encode_lbe(pcie_tr.lastbe));
        address = pcie_tr.low_addr;
        length  = pcie_tr.len;
        index   = 0;
        byte_count = length*4 - lbe - address[1:0];

        pcie_data = uvm_logic_vector_array::sequence_item #(32)::type_id::create("frame");
        assert(pcie_data.randomize() with {pcie_data.data.size() == pcie_tr.len; });


        while (length) begin
            comp_hdr  = uvm_logic_vector::sequence_item#(PCIE_DOWNHDR_WIDTH)::type_id::create("comp_hdr");
            comp_data = uvm_logic_vector_array::sequence_item#(32)::type_id::create("comp_data");
            /* Generate number of RCB blocks for this completion (between 1 and all remaining RCB for read request) */
            rcbs = $urandom_range((length + (address[LOW_ADDR_WIDTH-1 : 2] & (RCB/4-1)) + RCB/4-1) / (RCB/4), 1);

            /* Always use first segment: align to RCB */
            comp_length = min(RCB/4 - (address[LOW_ADDR_WIDTH-1 : 2] & (RCB/4-1)), length);

            /* Compute maximal allowed length of current transaction */
            for (int i = 1; i < rcbs; i++) begin
                /* Select smaller value between RCB and remaining length of request */
                l = min(RCB/4, length - comp_length);

                comp_length += l;
            end

            if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
                comp_hdr.data = {pcie_tr.req_id, pcie_tr.tag, 1'b0, address, completer_id, complete_st, bcm, byte_count,
                                 8'b01001010, pcie_tr.tag_9, pcie_tr.tc, pcie_tr.tag_8, pcie_tr.padd_0,
                                 pcie_tr.td, pcie_tr.ep, pcie_tr.relaxed, pcie_tr.snoop, pcie_tr.at, comp_length};

                debug_msg = {debug_msg, $sformatf("\n\t ============= RC PCIE MVB ================== \n")};
                debug_msg = {debug_msg, $sformatf("\n\t Generated RC request MVB number %d: %s\n",  mvb_cnt, comp_hdr.convert2string())};
                debug_msg = {debug_msg, $sformatf("\n\t Deparsed RC MVB TR: \n")};

                debug_msg = {debug_msg, $sformatf("\n\t PACKET SIZE:       %0d",  pcie_tr.len)};
                debug_msg = {debug_msg, $sformatf("\n\t LEN OF PART:       %0d",  comp_length)};
                debug_msg = {debug_msg, $sformatf("\n\t ATRIBUTES:        0x%h",  pcie_tr.at)};
                debug_msg = {debug_msg, $sformatf("\n\t SNOOP:            0x%h",  pcie_tr.snoop)};
                debug_msg = {debug_msg, $sformatf("\n\t RELAXED:          0x%h",  pcie_tr.relaxed)};
                debug_msg = {debug_msg, $sformatf("\n\t ERROR POISON:     0x%h",  pcie_tr.ep)};
                debug_msg = {debug_msg, $sformatf("\n\t TD:               0x%h",  pcie_tr.td)};
                debug_msg = {debug_msg, $sformatf("\n\t PADD0:            0x%h",  pcie_tr.padd_0)};
                debug_msg = {debug_msg, $sformatf("\n\t TAG_8:            0x%h",  pcie_tr.tag_8)};
                debug_msg = {debug_msg, $sformatf("\n\t TRAFFIC CLASS:    0x%h",  pcie_tr.tc)};
                debug_msg = {debug_msg, $sformatf("\n\t TAG_9:            0x%h",  pcie_tr.tag_9)};
                debug_msg = {debug_msg, $sformatf("\n\t CONST:            0x%h",  8'b01001010)};
                debug_msg = {debug_msg, $sformatf("\n\t BYTE CNT:         0x%h",  byte_count)};
                debug_msg = {debug_msg, $sformatf("\n\t BYTE CNT HDR:     0x%h",  comp_hdr.data[43 : 32])};
                debug_msg = {debug_msg, $sformatf("\n\t BCM:              0x%h",  bcm)};
                debug_msg = {debug_msg, $sformatf("\n\t COMPLETE STATUS:  0x%h",  complete_st)};
                debug_msg = {debug_msg, $sformatf("\n\t COMPLETER ID:     0x%h",  completer_id)};
                debug_msg = {debug_msg, $sformatf("\n\t LOW ADDRESS:      0x%h",  address)};
                debug_msg = {debug_msg, $sformatf("\n\t CONST:            0x%h",  1'b0)};
                debug_msg = {debug_msg, $sformatf("\n\t TAG:              0x%h",  pcie_tr.tag)};
                debug_msg = {debug_msg, $sformatf("\n\t REQUEST ID:       0x%h",  pcie_tr.req_id)};

                // $write("\n\t BYTE CNT:         0x%h", comp_hdr.data[43 : 32]);

                comp_data.data = new[comp_length];
                if (pcie_data != null) begin
                    for (int i = 0; i < comp_length; i++)
                        comp_data.data[i] = pcie_data.data[index + i];
                end

            end else begin
                if (length - comp_length == 0)
                    completed = 1'b1;
                else
                    completed = 1'b0;

                comp_hdr.data = {1'b0, pcie_tr.relaxed, pcie_tr.snoop, pcie_tr.tc, 1'b0, completer_id, pcie_tr.tag,
                                 pcie_tr.req_id, 1'b0, 1'b0, complete_st, comp_length, 1'b0, completed, 1'b0, byte_count, 4'b0000, address};
                // [11 : 0]  Lower Address
                // [15 : 12] Error Code
                // [28 : 16] Byte Count
                // [29]      Locked Read Completition
                // [30]      Request Completed // TODO
                // [31]      RESERVED
                // [42 : 32] Dword Count
                // [45 : 43] Completition Status
                // [46]      Poisoned Completition
                // [47]      RESERVED
                // [63 : 48] Requester ID
                // [71 : 64] Tag
                // [87 : 72] Completer ID
                // [88]      RESERVED
                // [91 : 89] Transaction Class
                // [94 : 92] Attributes

                debug_msg = {debug_msg, $sformatf("\n\t ============= RC PCIE MFB ================== \n")};
                debug_msg = {debug_msg, $sformatf("\t LOW ADDR            0x%h \n",  comp_hdr.data[11 : 0])};
                debug_msg = {debug_msg, $sformatf("\t ERROR CODE          0x%h \n",  comp_hdr.data[15 : 12])};
                debug_msg = {debug_msg, $sformatf("\t BYTE CNT            0x%h \n",  comp_hdr.data[28 : 16])};
                debug_msg = {debug_msg, $sformatf("\t REQUEST COMPLETED   0x%h \n",  comp_hdr.data[30])};
                debug_msg = {debug_msg, $sformatf("\t DWORD COUNT         0x%h \n",  comp_hdr.data[42 : 32])};
                debug_msg = {debug_msg, $sformatf("\t COMPLETITION STATUS 0x%h \n",  comp_hdr.data[45 : 43])};
                debug_msg = {debug_msg, $sformatf("\t REQUESTER ID        0x%h \n",  comp_hdr.data[63 : 48])};
                debug_msg = {debug_msg, $sformatf("\t TAG                 0x%h \n",  comp_hdr.data[71 : 64])};
                debug_msg = {debug_msg, $sformatf("\t TAG                 0x%h \n",  pcie_tr.tag)};
                debug_msg = {debug_msg, $sformatf("\t COMPLETER ID         %0d \n",  comp_hdr.data[87 : 72])};
                debug_msg = {debug_msg, $sformatf("\t TR CLASS             %0d \n",  comp_hdr.data[91 : 89])};
                debug_msg = {debug_msg, $sformatf("\t ATTRIBUTES           %0d \n",  comp_hdr.data[94 : 92])};
                debug_msg = {debug_msg, $sformatf("\t DOWN SEQ           :  %s \n",  comp_hdr.convert2string())};

                comp_data.data = new[comp_length + (PCIE_DOWNHDR_WIDTH/32)];
                comp_data.data[0 : 3-1] = {<<32{comp_hdr.data}};
                if (pcie_data != null) begin
                    for (int i = 0; i < comp_length; i++)
                        comp_data.data[i+3] = pcie_data.data[index + i];
                end
            end

            if (length - comp_length == 0) begin
                byte_count -= (comp_length*4 - address[1:0] - lbe);
            end else begin
                byte_count -= (comp_length*4 - address[1:0]);
            end

            length -= comp_length;
            mfb_cnt++;
            mvb_cnt++;
            index                         += comp_length;
            address[LOW_ADDR_WIDTH-1 : 2] += comp_length;
            address[1 : 0]                 = 2'b00;

            byte_array.push_back(comp_data);
            logic_array.push_back(comp_hdr);

        end
        `uvm_info(this.get_full_name(), debug_msg ,UVM_MEDIUM);

    endtask

    function logic[LOW_ADDR_WIDTH-1 : 0] count_low_addr(logic[64 : 0] global_id, logic [4-1 : 0] be);
        logic[LOW_ADDR_WIDTH-1 : 0] ret; // low address
        logic[2-1 : 0] lab; // low address bits
        lab = sv_dma_bus_pack::encode_fbe(be);
        ret = {global_id[LOW_ADDR_WIDTH-1 : 2], lab};
        return ret;
    endfunction

    //function uvm_logic_vector_array::sequence_item#(32) gen_data (uvm_logic_vector::sequence_item#(ITEM_WIDTH) req);

    //    uvm_logic_vector_array::sequence_item#(32) frame;
    //    frame = uvm_logic_vector_array::sequence_item #(32)::type_id::create("frame");

    //    if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
    //        assert(frame.randomize() with {frame.data.size() == int'(req.data[10-1 : 0]); });
    //    end else begin
    //        assert(frame.randomize() with {frame.data.size() == int'(req.data[75-1 : 64]); });
    //    end

    //    return frame;

    //endfunction

    function uvm_ptc_info_rc::sequence_item #(DEVICE) gen_hdr (uvm_logic_vector::sequence_item#(ITEM_WIDTH) req);

        uvm_ptc_info_rc::sequence_item #(DEVICE) pcie_tr;
        pcie_tr = uvm_ptc_info_rc::sequence_item #(DEVICE)::type_id::create("pcie_tr");

        if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
            pcie_tr.global_id = req.data[96-1 : 64]; // GLOBAL ID + PADDING 00
            pcie_tr.req_id    = req.data[64-1 : 48]; // same
            pcie_tr.tag       = req.data[48-1 : 40]; // same
            pcie_tr.lastbe    = req.data[40-1 : 36];
            pcie_tr.firstbe   = req.data[36-1 : 32];
            pcie_tr.fmt       = req.data[32-1 : 29];
            pcie_tr.type_n    = req.data[29-1 : 24];
            pcie_tr.tag_9     = req.data[23];
            pcie_tr.tc        = req.data[23-1 : 20];
            pcie_tr.tag_8     = req.data[19];
            pcie_tr.padd_0    = req.data[19-1 : 16];
            pcie_tr.td        = req.data[15];
            pcie_tr.ep        = req.data[14];
            pcie_tr.relaxed   = req.data[13];
            pcie_tr.snoop     = req.data[12];
            pcie_tr.at        = req.data[12-1 : 10];
            pcie_tr.len       = req.data[10-1 : 0];
        end else begin
            pcie_tr.global_id = req.data[64-1 : 2]; // GLOBAL ID + PADDING 00
            pcie_tr.len       = req.data[75-1 : 64];
            pcie_tr.relaxed   = req.data[125];
            pcie_tr.snoop     = req.data[124];
            pcie_tr.tc        = req.data[124-1 : 121];
            pcie_tr.tag       = req.data[104-1 : 96]; // same
            pcie_tr.req_id    = req.data[96-1 : 80]; // same
            if (RQ_TUSER_WIDTH == 60) begin
                pcie_tr.firstbe   = req.data[132-1 : 128];
                pcie_tr.lastbe    = req.data[136-1 : 132];
            end else begin
                pcie_tr.firstbe   = req.data[136-1 : 128];
                pcie_tr.lastbe    = req.data[144-1 : 136];
            end
            pcie_tr.fmt       = '0;
            pcie_tr.type_n    = '0;
            pcie_tr.tag_9     = '0;
            pcie_tr.tag_8     = '0;
            pcie_tr.padd_0    = '0;
            pcie_tr.td        = '0;
            pcie_tr.ep        = '0;
            pcie_tr.at        = '0;
        end

        pcie_tr.low_addr = count_low_addr(pcie_tr.global_id, pcie_tr.firstbe);

        return pcie_tr;

    endfunction

    virtual function void write(uvm_logic_vector::sequence_item#(ITEM_WIDTH) req);
        headers.push_back(req);
    endfunction

    virtual task run_phase(uvm_phase phase);
        uvm_logic_vector::sequence_item#(ITEM_WIDTH) header;
        int wait_time = 0;
        pcie_info pcie_tr;

        forever begin
            int unsigned item_index;
            wait_time = $urandom_range(20, 0);

            #(wait_time*(2*CLK_PERIOD));
            wait(headers.size() != 0);

            /* TODO: enable this and delete next block
            item_index = $urandom_range(headers.size());
            header = headers[item_index];
            headers.delete(item_index);
            */

            headers.shuffle();
            header = headers.pop_front();

            pcie_tr.hdr  = gen_hdr(header);
            //pcie_tr.data = gen_data(header);
            split(pcie_tr.hdr);
        end
    endtask

endclass
