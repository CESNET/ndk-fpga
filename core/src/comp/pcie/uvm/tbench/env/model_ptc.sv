// model_ptc.sv: Model of ptc
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz> 

// SPDX-License-Identifier: BSD-3-Clause



class tag_register#(int unsigned TAG_WIDTH) extends uvm_object;
    `uvm_object_param_utils(uvm_pcie_top::tag_register#(TAG_WIDTH))

    typedef struct {
        int unsigned port;
        int unsigned length;
        int unsigned unit_id;
        logic [TAG_WIDTH] tag;
    } dma_info_t;

    //TAGS
    protected logic [TAG_WIDTH-1:0] dma2pcie[logic [8+TAG_WIDTH-1:0]];
    protected dma_info_t            pcie2dma[logic [TAG_WIDTH-1:0]];

    function new(string name = "tag_register");
        super.new(name);
    endfunction

    function void register_pcie_tag(int unsigned type_tr, int unsigned length, logic [8-1:0] unit_id, logic [TAG_WIDTH-1:0] dma_tag, logic [TAG_WIDTH-1:0] pcie_tag);
        dma_info_t info;

        `uvm_info(this.get_full_name(), $sformatf("\nTAG REGISTER\n\tTYPE %0d\n\tlength %0d\n\tunit ID %0d(0x%h)\n\tdma tag %0d(0x%h)\n\tpcie tag %0d(0x%h)",
                                        type_tr, length, unit_id, unit_id, dma_tag, dma_tag, pcie_tag, pcie_tag), UVM_DEBUG);
        if (type_tr == 0) begin
            //check if there isnt
            if (pcie2dma.exists(pcie_tag)) begin
                `uvm_error(this.get_full_name(), $sformatf("\n\tPCIE tag %0d(0x%h) already exists", pcie_tag, pcie_tag));
            end else if (dma2pcie.exists({unit_id, dma_tag})) begin
                `uvm_error(this.get_full_name(), $sformatf("\n\tDMA unit id 0x%h tag %0d(0x%h) already exists", unit_id, dma_tag, dma_tag));
            end else begin
                //dma to pcie
                dma2pcie[{unit_id, dma_tag}] = pcie_tag;

                //pcie to dma
                info.port    = -1;
                info.length  = length;
                info.unit_id = unit_id;
                info.tag     = dma_tag;

                pcie2dma[pcie_tag] = info;
            end
        end
    endfunction

    task get_dma2pcie(input logic type_tr, int unsigned dma_port, logic [TAG_WIDTH-1:0] dma_tag, logic [8-1:0] dma_unit_id, output logic [TAG_WIDTH-1:0] pcie_tag);
        `uvm_info(this.get_full_name(), $sformatf("\nTAG TRANSLATE DMA TO PCIE\n\ttype %0d\n\tdma port %0d \n\tdma tag %0d(0x%h)\n\tunit id %0d(0x%h)",
                                                 type_tr, dma_port, dma_tag, dma_tag, dma_unit_id, dma_unit_id), UVM_FULL);
        if (type_tr == 0) begin

            wait(dma2pcie.exists({dma_unit_id, dma_tag}));
            pcie_tag = dma2pcie[{dma_unit_id, dma_tag}];
            pcie2dma[pcie_tag].port = dma_port;

        end else begin
            pcie_tag = 0;
        end
    endtask

    function dma_info_t get_pcie2dma(logic [TAG_WIDTH-1:0] pcie_tag, int unsigned last);
        dma_info_t info;

        `uvm_info(this.get_full_name(), $sformatf("\nTAG TRANSLATE PCIE TO DMA \n\tpcie tag %0d(0x%h)\n\tlast %0d", pcie_tag, pcie_tag, last), UVM_FULL);


        if (!pcie2dma.exists(pcie_tag)) begin
            `uvm_error(this.get_full_name(), $sformatf("\n\tPCIE tag doesnt exist %0d(0x%h)", pcie_tag, pcie_tag));
        end else begin
            info = pcie2dma[pcie_tag];
            if (last) begin
                pcie2dma.delete(pcie_tag);
                dma2pcie.delete({info.unit_id, info.tag});
            end
        end

        return info;
    endfunction

    //---------------------------------------
    // OTHERS METHODS
    //---------------------------------------
    function int unsigned used();
        return (dma2pcie.size() != 0 || pcie2dma.size() != 0);
    endfunction


endclass


////////////////////////////////////////////////////
//This is probe which probe transating from dma tag to pcie tag
class tag_cbs #(int unsigned REGIONS, int unsigned TAG_WIDTH) extends uvm_event_callback;
    `uvm_object_param_utils(uvm_pcie_top::tag_cbs #(REGIONS, TAG_WIDTH))

    uvm_pcie_top::tag_register#(TAG_WIDTH) registration;
    //protected logic [TAG_WIDTH-1:0] tag_translation[logic [8+TAG_WIDTH-1:0]];

    protected int unsigned transactions;
    function new(string name = "");
        super.new(name);
        transactions = 0;
    endfunction

    //---------------------------------------
    // pre trigger method
    //---------------------------------------
    virtual function bit pre_trigger(uvm_event e, uvm_object data);
        return 0;
    endfunction

    //---------------------------------------
    // post trigger method
    //---------------------------------------
    virtual function void post_trigger(uvm_event e, uvm_object data);
        uvm_probe::data#(REGIONS*(1 + TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) c_data;
        logic [REGIONS-1:0]           vld;
        logic [REGIONS*TAG_WIDTH-1:0] tags;
        logic [REGIONS*sv_dma_bus_pack::DMA_UPHDR_WIDTH-1:0] dma_hdr;

        $cast(c_data, data);
        {dma_hdr, tags, vld} = c_data.data;
        for (int unsigned it = 0; it < REGIONS; it++) begin
            if (vld[it] == 1) begin
                logic [TAG_WIDTH-1:0] tag_act                            = tags   [(it+1)*TAG_WIDTH-1 -: TAG_WIDTH];
                logic [sv_dma_bus_pack::DMA_UPHDR_WIDTH-1:0] dma_hdr_act = dma_hdr[(it+1)*sv_dma_bus_pack::DMA_UPHDR_WIDTH-1 -: sv_dma_bus_pack::DMA_UPHDR_WIDTH];
                uvm_ptc_info::sequence_item act_dma_hdr;

                act_dma_hdr = new();
                act_dma_hdr.relaxed     = dma_hdr_act[sv_dma_bus_pack::DMA_REQUEST_W-1 : sv_dma_bus_pack::DMA_REQUEST_RELAXED_O];
                act_dma_hdr.pasidvld    = dma_hdr_act[sv_dma_bus_pack::DMA_REQUEST_PASIDVLD_O];
                act_dma_hdr.pasid       = dma_hdr_act[sv_dma_bus_pack::DMA_REQUEST_PASID_O];
                act_dma_hdr.vfid        = dma_hdr_act[sv_dma_bus_pack::DMA_REQUEST_PASID_O-1 : sv_dma_bus_pack::DMA_REQUEST_VFID_O];
                act_dma_hdr.global_id   = dma_hdr_act[sv_dma_bus_pack::DMA_REQUEST_VFID_O-1 : sv_dma_bus_pack::DMA_REQUEST_GLOBAL_O];
                act_dma_hdr.unitid      = dma_hdr_act[sv_dma_bus_pack::DMA_REQUEST_GLOBAL_O-1 : sv_dma_bus_pack::DMA_REQUEST_UNITID_O];
                act_dma_hdr.tag         = dma_hdr_act[sv_dma_bus_pack::DMA_REQUEST_UNITID_O-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_O];
                act_dma_hdr.lastib      = dma_hdr_act[sv_dma_bus_pack::DMA_REQUEST_TAG_O-1 : sv_dma_bus_pack::DMA_REQUEST_LASTIB_O];
                act_dma_hdr.firstib     = dma_hdr_act[sv_dma_bus_pack::DMA_REQUEST_LASTIB_O-1 : sv_dma_bus_pack::DMA_REQUEST_FIRSTIB_O];
                act_dma_hdr.type_ide    = dma_hdr_act[sv_dma_bus_pack::DMA_REQUEST_FIRSTIB_O-1 : sv_dma_bus_pack::DMA_REQUEST_TYPE_O];
                act_dma_hdr.length      = dma_hdr_act[sv_dma_bus_pack::DMA_REQUEST_TYPE_O-1 : sv_dma_bus_pack::DMA_REQUEST_LENGTH_O]; // Size in DWORDS

                transactions++;
                `uvm_info(this.get_full_name(), $sformatf("\n\tTag translaction %0d WR(%0d) DMA TAG : 0x%h DMA ID : 0x%h => PCIE tag 0x%h", transactions, act_dma_hdr.type_ide, act_dma_hdr.tag, act_dma_hdr.unitid, tag_act), UVM_HIGH);

                if ($isunknown(tag_act)) begin
                    `uvm_error(this.get_full_name(), $sformatf("\n\tUndefined Value in TAG assigment 0x%h", tag_act));
                end

                registration.register_pcie_tag(act_dma_hdr.type_ide, act_dma_hdr.length*4, act_dma_hdr.unitid, act_dma_hdr.tag, tag_act);
            end
        end
    endfunction
endclass


class model_ptc_config;
    string path;
endclass

class model_ptc#(RQ_REGIONS, DMA_PORTS, ITEM_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_pcie_top::model_ptc#(RQ_REGIONS, DMA_PORTS, ITEM_WIDTH))

    localparam int unsigned PTC_TAG_WIDTH     = 8;

    uvm_analysis_port     #(uvm_pcie::request_header)   pcie_rq;
    uvm_tlm_analysis_fifo #(uvm_pcie::completer_header) pcie_rc;

    uvm_tlm_analysis_fifo #(uvm_dma::sequence_item_rq) dma_rq[DMA_PORTS];
    uvm_analysis_port     #(uvm_dma::sequence_item_rc) dma_rc[DMA_PORTS];

    protected uvm_pcie_top::tag_cbs #(RQ_REGIONS, PTC_TAG_WIDTH) tags_cbs;
    protected uvm_pcie_top::tag_register#(PTC_TAG_WIDTH)  tags;
    protected int unsigned rq_transactions[DMA_PORTS];
    protected int unsigned rc_transactions;
    protected model_ptc_config cfg; 

    function new(string name, uvm_component parent = null);
        super.new(name, parent);

        pcie_rq = new("pcie_rq", this);
        pcie_rc = new("pcie_rc", this);
        rc_transactions = 0;

        for (int dma = 0; dma < DMA_PORTS; dma++) begin
            string i_string;
            i_string.itoa(dma);

            dma_rq[dma] = new({"dma_rq_", i_string}, this);
            dma_rc[dma] = new({"dma_rc_", i_string}, this);
            rq_transactions[dma] = 0;
        end
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (pcie_rc.used() != 0);

        for (int unsigned it = 0; it < DMA_PORTS; it++) begin
            ret |= (dma_rq[it].used()  != 0);
        end
        return ret;
    endfunction

    function int unsigned success();
        int unsigned ret = 1;
        return ret;
    endfunction


    function void build_phase(uvm_phase phase);
        if (!uvm_config_db #(model_ptc_config)::get(this, "", "m_config", cfg)) begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot get configuration object");
        end

        tags_cbs = uvm_pcie_top::tag_cbs #(RQ_REGIONS, PTC_TAG_WIDTH)::type_id::create("tags_cbs", this);
        tags     = uvm_pcie_top::tag_register#(PTC_TAG_WIDTH)::type_id::create("tags", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        uvm_probe::pool::get_global_pool().get({ "probe_event_component_", cfg.path, ".probe_tag" }).add_callback(tags_cbs);
        tags_cbs.registration = tags;
    endfunction

    task run_rc();
        uvm_pcie::completer_header pcie_tr;
        uvm_dma::sequence_item_rc dma_tr;
        logic completed;
        logic [PTC_TAG_WIDTH-1:0] pcie_tag;
        int unsigned move;

        forever begin
            tag_register#(PTC_TAG_WIDTH)::dma_info_t dma_info;

            pcie_rc.get(pcie_tr);

            dma_tr = uvm_dma::sequence_item_rc::type_id::create("dma_tr", this);
            dma_tr.start = pcie_tr.start;

            rc_transactions++;
            `uvm_info(this.get_full_name(), $sformatf("\nGET PCIE RC TRANSACTION %0d %s", rc_transactions, pcie_tr.convert2string()), UVM_FULL);

            move       = pcie_tr.lower_address & 2'b11;
            pcie_tag   = pcie_tr.tag;
            completed  = (pcie_tr.byte_count <= (pcie_tr.length*4 - move));

            dma_info              = tags.get_pcie2dma(pcie_tag, completed);
            dma_tr.length    = pcie_tr.length;
            dma_tr.completed = completed;
            dma_tr.tag       = dma_info.tag;
            dma_tr.unit_id   = dma_info.unit_id;
            dma_tr.data      = pcie_tr.data;
            `uvm_info(this.get_full_name(), $sformatf("\nDMA RC PORT %0d %s", dma_info.port, dma_tr.convert2string()), UVM_FULL);

            dma_rc[dma_info.port].write(dma_tr);
        end

    endtask

    task run_rq(int unsigned dma);
        uvm_dma::sequence_item_rq rq_tr;
        uvm_pcie::request_header  rsp_tr;
        int unsigned rq_tr_tmp;

        forever begin
            dma_rq[dma].get(rq_tr);

            rsp_tr       = uvm_pcie::request_header::type_id::create("rsp_tr", this);
            rsp_tr.start = rq_tr.start;

            rq_transactions[dma]++;
            rq_tr_tmp = rq_transactions[dma];

            rsp_tr.fmt        = {1'b0, rq_tr.hdr.type_ide, rq_tr.hdr.global_id[64-1:0] != 32'b0 ? 1'b1 : 1'b0};
            rsp_tr.pcie_type  = 5'b0;

            //rq_tr.hdr.unitid // NOT USED

            `uvm_info(this.get_full_name(), $sformatf("\nGET DMA RX [%0d] TRANSACTION %0d %s", dma, rq_tr_tmp, rq_tr.convert2string()), UVM_FULL);

            rsp_tr.traffic_class     = 0;
            rsp_tr.id_based_ordering = 0;
            rsp_tr.relaxed_ordering  = rq_tr.hdr.relaxed;
            rsp_tr.no_snoop          = 0;
            rsp_tr.th                = 0;
            rsp_tr.td                = 0;
            rsp_tr.ep                = 0;
            rsp_tr.at                = 0;
            rsp_tr.length            = rq_tr.hdr.length;
            rsp_tr.data              = rq_tr.hdr.type_ide == 1'b1 ? rq_tr.data : {};
            rsp_tr.requester_id      = {8'b0,  rq_tr.hdr.vfid};
            tags.get_dma2pcie(rq_tr.hdr.type_ide, dma, rq_tr.hdr.tag, rq_tr.hdr.unitid, rsp_tr.tag);
            case(rq_tr.hdr.lastib) 
                0 : rsp_tr.lbe = 4'b1111;
                1 : rsp_tr.lbe = 4'b0111;
                2 : rsp_tr.lbe = 4'b0011;
                3 : rsp_tr.lbe = 4'b0001;
                default : rsp_tr.lbe = 'x;
            endcase
            case(rq_tr.hdr.firstib) 
                0 : rsp_tr.fbe = 4'b1111;
                1 : rsp_tr.fbe = 4'b1110;
                2 : rsp_tr.fbe = 4'b1100;
                3 : rsp_tr.fbe = 4'b1000;
                default : rsp_tr.lbe = 'x;
            endcase
            rsp_tr.lbe               = (rsp_tr.length != 1) ? rsp_tr.lbe : 0;
            rsp_tr.address           = rq_tr.hdr.global_id[64-1:2];
            rsp_tr.ph                = 0;


            `uvm_info(this.get_full_name(), $sformatf("\nPCIE RQ transaction %0d %s", rq_tr_tmp,  rsp_tr.convert2string()), UVM_MEDIUM);
            //change tag and pic
            pcie_rq.write(rsp_tr);
        end
    endtask

    task run_phase(uvm_phase phase);
        fork
             run_rc();
        join_none

        for (int dma = 0; dma < DMA_PORTS; dma++) begin
            fork
                automatic int unsigned index = dma;
                run_rq(index);
            join_none
        end
    endtask

    function void check_phase(uvm_phase phase);
        string msg;

        if (this.success() == 0 || this.used()) begin
            msg = $sformatf("\n\tSuccess %0d Transaction in\n\t\tPcie RC : %0d", this.success(), pcie_rc.used());

            for (int unsigned it = 0; it < DMA_PORTS; it++) begin
                msg = {msg, $sformatf("\n\t\tdma rq [%0d] : %0d", it,  dma_rq[it].used())};
            end
            `uvm_error(this.get_full_name(), msg);
        end
    endfunction

endclass


