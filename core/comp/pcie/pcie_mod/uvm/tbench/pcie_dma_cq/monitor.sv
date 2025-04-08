// monitor.sv: pcie monitor
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class monitor#(ITEM_WIDTH, DEVICE) extends uvm_pcie::monitor;
    `uvm_component_param_utils(uvm_pcie_dma_cq::monitor#(ITEM_WIDTH, DEVICE))

    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))                      cq_data;
    uvm_tlm_analysis_fifo#(uvm_logic_vector::sequence_item#(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)) cq_meta;
    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))                      cc_data;
    uvm_tlm_analysis_fifo#(uvm_logic_vector::sequence_item#(sv_pcie_meta_pack::PCIE_CC_META_WIDTH)) cc_meta;

    localparam int unsigned HDR_WIDTH       = 128;
    localparam int unsigned PREFIX_WIDTH    = 32;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);

        cq_data = new("cq_data", this);
        cq_meta = new("cq_meta", this);
        cc_data = new("cc_data", this);
        cc_meta = new("cc_meta", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;

        ret |= cq_data.used();
        ret |= cq_meta.used();
        ret |= cc_data.used();
        ret |= cc_meta.used();
        return ret;
    endfunction

    task run_cq();
        forever begin
            logic r0, r1, r2;
            logic [128-1:0] hdr;

            uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)                      item_data;
            uvm_logic_vector::sequence_item#(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH) item_meta;
            uvm_pcie_extend::request_header item;

            item = uvm_pcie_extend::request_header::type_id::create("item", this);

            if (DEVICE == "AGILEX") begin
                cq_meta.get(item_meta);
                cq_data.get(item_data);

                item.time_array_add(item_meta.start);
                item.time_array_add(item_data.start);

                //item = uvm_pcie::request_header::type_id::create("item", this);
                hdr = {item_meta.data[32-1:0], item_meta.data[64-1:32], item_meta.data[96-1:64], item_meta.data[128-1:96]};

                item.bar  = item_meta.data[162:160];
                item.bar_aperture = 26;
                item.vf   = 0;
                item.address = 0;

                //prefix = item_meta.data[160-1:128];
                {item.fmt, item.pcie_type, r0, item.traffic_class, r1, item.id_based_ordering, r2, item.th, item.td, item.ep, item.relaxed_ordering, item.no_snoop, item.at, item.length} = hdr[32*4-1 -: 32];
                if (item.fmt[0] == 1'b0) begin
                    {item.requester_id, item.tag, item.lbe, item.fbe, item.address[32-1:2], item.ph} = hdr[32*3-1 -: 64];
                end else begin
                    {item.requester_id, item.tag, item.lbe, item.fbe, item.address, item.ph}         = hdr[32*3-1 -: 96];
                end

                if (item.fmt[3-1:1] == 2'b01) begin
                    item.data = item_data.data;
                end else begin
                    item.data = {};
                end
            end else if (DEVICE == "ULTRASCALE") begin
                logic [4-1:0] fbe;
                logic [4-1:0] lbe;
                logic [1-1:0] thp_present;
                logic [2-1:0] thp_type;
                logic [8-1:0] thp_tag;
                logic [2-1:0]  at;
                logic [64-1:2] address;
                logic [11-1:0] length;
                logic [4-1:0]  req_type;
                logic [1-1:0]  poisoned_req;
                logic [16-1:0] requester_id;
                logic [8-1:0]  tag;
                logic [16-1:0] completer_id;
                logic [1-1:0]  requester_id_en;
                logic [3-1:0]  tc;
                logic [3-1:0]  attr;
                logic [1-1:0]  ecrc;

                cq_meta.get(item_meta);
                cq_data.get(item_data);

                item.time_array_add(item_meta.start);
                item.time_array_add(item_data.start);

                {ecrc, attr, tc, requester_id_en, completer_id, tag, requester_id, poisoned_req, req_type, length,
                address, at}
                = {item_data.data[3], item_data.data[2], item_data.data[1], item_data.data[0]};

                item.at       = at;
                item.address  = address;
                item.length   = length;
                item.fbe      = 4'b1111;
                item.lbe      = (length != 1) ? 4'b1111 : 0;
                item.fmt[0]   = (address[64-1:32] != 0);
                if (req_type === 4'b0000) begin
                    item.fmt[3-1:1] = 2'b00;
                    item.pcie_type  = 5'b00000;
                end else if (req_type === 4'b0001) begin
                    item.fmt[3-1:1] = 2'b01;
                    item.pcie_type  = 5'b00000;
                end else begin
                    `uvm_fatal(this.get_full_name(), "\n\tUnknow pcie transaction type");
                end

                item.ph           = 0;
                item.th           = 0;
                item.td           = 0;
                item.ep           = poisoned_req;
                item.requester_id = requester_id;
                item.tag          = tag;
                item.traffic_class     = tc;
                item.id_based_ordering = attr[2];
                item.relaxed_ordering  = attr[1];
                item.no_snoop          = attr[0];

                item.data = new[item_data.data.size()-4];
                for (int unsigned it = 4; it < item_data.data.size(); it++) begin
                   item.data[it-4] = item_data.data[it];
                end

                //-- 171 to 171     TPH_PRESENT  Transaction Processing Hint (TPH) present flag - Xilinx FPGA only
                //-- 172 to 173     TPH_TYPE     The PH field associated with the hint - Xilinx FPGA only
                //-- 174 to 181     TPH_ST_TAG   The Steering Tag associated with the hint - Xilinx FPGA only
                {thp_tag, thp_type, thp_present, lbe, fbe} = item_meta.data[182-1:163];

                item.fbe = fbe;
                item.lbe = lbe;

                if (thp_present !== 1'b0) begin
                    `uvm_fatal(this.get_full_name(), $sformatf("\n\tUnsupported feature THP_PRESENT(%0d) : %s", thp_present, DEVICE));
                end
            end else begin
                `uvm_fatal(this.get_full_name(), $sformatf("\n\tUnsupported device : %s", DEVICE));
            end

            cq_analysis_port.write(item);
        end
    endtask

    task run_cc();
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data;
        uvm_logic_vector::sequence_item#(sv_pcie_meta_pack::PCIE_CC_META_WIDTH)  meta;

        forever begin
            logic [HDR_WIDTH-1:0]        hdr_orig;
            logic [HDR_WIDTH-1:0]        hdr;
            logic [PREFIX_WIDTH-1:0]     prefix;

            logic [3-1:0] fmt;
            logic [5-1:0] pcie_type;
            logic [1-1:0] r0;
            logic [3-1:0] tc;
            logic [1-1:0] r1;
            logic [3-1:0] attr;
            logic [1-1:0] r2;
            logic [1-1:0] th;
            logic [1-1:0] td;
            logic [1-1:0] ep;
            logic [2-1:0] at;
            logic [10-1:0] length;

            uvm_pcie::completer_header item;

            item = uvm_pcie::completer_header::type_id::create("item", this);

            if (DEVICE == "AGILEX") begin
                logic [16-1:0] completer_id;
                logic [3-1:0]  compl_status;
                logic [1-1:0]  bcm;
                logic [12-1:0] byte_count;
                logic [16-1:0] requester_id;
                logic [8-1:0]  tag;
                logic [1-1:0]  r0;
                logic [7-1:0]  lower_address;

                cc_meta.get(meta);
                cc_data.get(data);

                item.time_array_add(meta.start);
                item.time_array_add(data.start);

                {prefix, hdr_orig} = meta.data;
                hdr = {hdr_orig[32-1:0], hdr_orig[64-1:32], hdr_orig[96-1:64], hdr_orig[128-1:96]};
                {fmt, pcie_type, r0, tc, r1, attr[2], r2, th, td, ep, attr[2-1:0], at, length} = hdr[32*4-1 -: 32];

                {completer_id, compl_status, bcm, byte_count, requester_id, tag, r0, lower_address} = hdr[32*3-1 -: 64];

                item.fmt               = fmt;
                item.pcie_type         = pcie_type;
                item.traffic_class     = tc;
                item.id_based_ordering = attr[2];
                item.relaxed_ordering  = attr[1];
                item.no_snoop          = attr[0];
                item.th                = th;
                item.td                = td;
                item.ep                = ep;
                item.at                = at;
                item.length            = length;
                item.completer_id      = completer_id;
                item.compl_status      = compl_status;
                item.bcm               = bcm;
                item.byte_count        = byte_count;
                item.requester_id      = requester_id;
                item.tag               = tag;
                item.lower_address     = lower_address;

                if (fmt[3-1:1] == 2'b01) begin
                    //avalon_down_data.get(data);
                    item.data = new[length];
                    for (int unsigned it = 0; it < length; it++) begin
                        item.data[it] = data.data[it];
                    end
                end
            end else if (DEVICE == "ULTRASCALE") begin
                logic [7-1:0] address;
                logic [1-1:0] r0;
                logic [2-1:0] at;
                logic [6-1:0] r1;
                logic [13-1:0] byte_count;
                logic [1-1:0] locked_read;
                logic [2-1:0] r2;
                logic [11-1:0] dword_count;
                logic [3-1:0] completion_status;
                logic [1-1:0] poisoned_completion;
                logic [1-1:0]  r3;
                logic [16-1:0] requester_id;
                logic [8-1:0] tag;
                logic [16-1:0] completer_id;
                logic [1-1:0] completer_id_en;
                logic [3-1:0] tc;
                logic [3-1:0] attr;
                logic [1-1:0] ecrc;

                cc_data.get(data);
                item.time_array_add(data.start);

                {ecrc, attr, tc, completer_id_en, completer_id, tag, requester_id, r3,
                poisoned_completion, completion_status, dword_count, r2, locked_read,
                byte_count, r1, at, r0, address}
                = {data.data[2], data.data[1], data.data[0]};

                item.fmt               = 3'b010;
                item.pcie_type         = 5'b01010;
                item.lower_address     = address;
                item.at                = at;
                item.th                = 0;
                item.td                = 0;
                item.ep                = poisoned_completion;
                item.requester_id      = requester_id;
                item.tag               = tag;
                item.completer_id      = completer_id;
                item.traffic_class     = tc;
                item.id_based_ordering = attr[2];
                item.relaxed_ordering  = attr[1];
                item.no_snoop          = attr[0];
                item.compl_status = completion_status;
                item.bcm          = 0;
                item.byte_count   = byte_count;
                item.length       = dword_count;

                item.data = new[data.data.size()-3];
                for (int unsigned it = 3; it < data.data.size(); it++) begin
                    item.data[it-3] = data.data[it];
                end
            end else begin
                `uvm_fatal(this.get_full_name(), $sformatf("\n\tUnsupported device : %s", DEVICE));
            end

            cc_analysis_port.write(item);
        end
    endtask

    task run_phase(uvm_phase phase);
        fork
            run_cq();
            run_cc();
        join
    endtask
endclass
