/*
 * avalon.sv intel pcie
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */


//////////////////////////////////////////////
//// Convert pcie_CQ to axi_CQ
//////////////////////////////////////////////
class pcie2avalon  extends pcie2common#(10);

    sv_common_pkg::tTransMbx outMbx;
    int unsigned verbose;

    function new (string inst, sv_common_pkg::tTransMbx inMbx);
        super.new(inst, inMbx);
        this.outMbx = new(1);
        this.verbose = 0;
    endfunction

    function void verbose_set(int unsigned level);
        this.verbose = level;
    endfunction

    function logic [127:0] gen_header(PcieRequest tr_in, bit write);
        logic [127:0] hdr;
        logic [9:0] tag = tr_in.tag;

        if (tr_in.addr[63:32] != '0) begin
            hdr[95:64]  = tr_in.addr[63:32];
            hdr[127:98] = tr_in.addr[31:2];
            hdr[97:96]  = 2'b00;

            hdr[31:29] = 3'b001;
        end else begin
            hdr[127:98] = '0;
            hdr[95:66]  = tr_in.addr[31:2];
            hdr[65:64]  = 2'b00;

            hdr[31:29] = 3'b000;
        end
        hdr[30]    = write; //RQ type
        hdr[63:48] = '0; //REQUESTER ID
        hdr[47:40] = tag[7:0];
        hdr[39:36] = tr_in.lbe; //last be
        hdr[35:32] = tr_in.fbe; //fist be
        hdr[28:24] = '0;
        hdr[23]    = tag[9];
        hdr[22:20] = 3'b000;
        hdr[19]    = tag[8];
        hdr[18:16] = '0;
        hdr[15]    = 1'b0;
        hdr[14]    = 1'b0;
        hdr[13:12] = 2'b00;
        hdr[11:10] = 2'b00;
        hdr[9:0]   = tr_in.length;

        return { <<32 {hdr}};
    endfunction

    task gen_read(PcieRequest tr_in);
        avst_tx::transaction tr_out;
        tr_out = new();
        tr_out.hdr = gen_header(tr_in, 1'b0);

        tr_out.data   = 'X;
        tr_out.prefix = '0;
        tr_out.sop    = 1;
        tr_out.eop    = 1;
        tr_out.empty  = '1;
        tr_out.valid  = 1;
        tr_out.bar_range = 0;
        outMbx.put(tr_out);
    endtask

    task gen_write(PcieRequest tr_in);
        avst_tx::transaction tr_out;
        int unsigned it_data = 0;

        tr_out = new();
        tr_out.hdr = gen_header(tr_in, 1'b1);
        tr_out.valid  = 1;
        tr_out.sop    = 1;
        tr_out.eop    = 0;
        tr_out.prefix = '0;
        tr_out.bar_range = 0;

        while ((it_data + 8) < tr_in.data.size()) begin
            tr_out.data = { <<32 {tr_in.data[it_data +: 8]}};
            it_data += 8;


            tr_out.prefix = '0;
            tr_out.empty  = '0;
            outMbx.put(tr_out);

            tr_out = new();
            tr_out.valid  = 1;
            tr_out.sop    = 0;
            tr_out.eop    = 0;
            tr_out.bar_range = 0;
        end


        for (int it = 0; it < tr_in.data.size() - it_data; it++) begin
            tr_out.data[(it + 1)*32-1 -: 32]  = tr_in.data[it_data + it];
        end
        tr_out.empty  = 7 - (tr_in.data.size() - it_data); //count
        tr_out.eop    = 1;
        outMbx.put(tr_out);
    endtask


    task run();
        PcieRequest tr_in;

        while (enabled) begin
            byte unsigned headerArray[16];
            byte unsigned data[];
            int unsigned  data_size;

            getTr(tr_in);

            if (verbose > 0) begin
                tr_in.display({inst, " SEND"});
            end

            if (tr_in.type_tr == PCIE_RQ_READ) begin
                gen_read(tr_in);
            end else begin
                gen_write(tr_in);
            end

            foreach (cbs[i]) begin
                cbs[i].post_tx(tr_in, inst);
            end

            ifg.randomize();
            if(ifg.enabled) begin
                int unsigned it = 0;
                while(it < ifg.length) begin
                    avst_tx::transaction tr_out = new();
                    tr_out.valid  = 0;
                    tr_out.sop    = 'X;
                    tr_out.eop    = 'X;
                    tr_out.bar_range = 'X;
                    tr_out.prefix = 'X;
                    tr_out.hdr    = 'X;
                    tr_out.data   = 'X;

                    outMbx.put(tr_out);
                    it++;
                end
            end
        end
    endtask
endclass

class avalon2pcie extends sv_common_pkg::MonitorCbs;

    typedef enum {NONE, RECIVE} status_t;
    status_t status;
    PcieCompletion tr_out;
    sv_common_pkg::MonitorCbs cbs[$];
    int verbose = 0;

    function new();
        status = NONE;
    endfunction

    function void verbose_set(int unsigned level);
        this.verbose = level;
    endfunction

    virtual task pre_rx(ref sv_common_pkg::Transaction transaction, string inst);
    endtask

    function void setCallbacks(sv_common_pkg::MonitorCbs cbs);
        this.cbs.push_back(cbs);
    endfunction

    function void sop_process(PcieCompletion ret, avst_rx::transaction tr);
        logic [15:0] request_id;
        logic [9:0]  tag;
        logic [6:0]  lower_addr;
        logic [15:0] completer_id;
        logic [2:0]  comp_status;
        logic [11:0] byte_count;
        logic [2:0]  traffic_class;
        logic [9:0]  dword_count;
        logic        td;
        logic        ep;
        logic [1:0]  attr;
        logic [2:0]  fmt;
        logic [4:0]  fmt_type;
        logic [127:0] hdr;

        hdr = { <<32 {tr.hdr}};
        dword_count   = hdr[9:0];
        attr          = hdr[13:12];
        ep            = hdr[14];
        td            = hdr[15];
        tag           = {hdr[23:23], hdr[19:19], hdr[79:72]};
        traffic_class = hdr[22:20];
        fmt           = hdr[31:29];
        fmt_type      = hdr[28:24];
        byte_count    = hdr[43:32];
        comp_status   = hdr[47:45];
        completer_id  = hdr[63:48];
        lower_addr    = hdr[70:64];
        request_id    = hdr[95:80];

        if (fmt != 3'b010 || fmt_type != 5'b01010) begin
            $error("Unknown response fmt %b type %b", fmt, fmt_type);
            $stop();
        end

        ret.tag = tag;
        ret.dword_count   = dword_count;
        ret.lower_address = lower_addr;
        ret.byte_count    = byte_count;
    endfunction

    virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
        avst_rx::transaction tr;

        $cast(tr, transaction);
        if (verbose > 4) begin
            tr.display({inst, " GET AVALON CC TRANSACTION"});
        end

        if (status == NONE && tr.sop == 1'b1) begin
            tr_out = new();
            foreach (cbs[i]) begin
                sv_common_pkg::Transaction tr_send;
                $cast(tr_send, tr_out);
                cbs[i].pre_rx(tr_send, inst);
            end

            sop_process(tr_out, tr);
            status = RECIVE;
        end

        if (status == RECIVE) begin
            logic [31:0] data[];
            { <<32 {data}} = tr.data;
            tr_out.data = {tr_out.data, data};
        end

        if (status == RECIVE && tr.eop == 1'b1) begin
            if (verbose > 0) begin
                tr_out.display({inst, " PCIE CC TRANSACTION"});
            end
            tr_out.data = new[tr_out.dword_count](tr_out.data);
            status = NONE;

            foreach (cbs[i]) begin
                sv_common_pkg::Transaction tr_send;
                $cast(tr_send, tr_out);
                cbs[i].post_rx(tr_send, inst);
            end
        end
    endtask
endclass

///////////////////////////////////////////////////
// IFG CONGIG AVALON
///////////////////////////////////////////////////
class ifg_config_avst_rx extends avst_rx::ifg_config;
    ifg_config_rand_setup cfg;

    function new (ifg_config_rand_setup cfg = null);
        this.cfg = cfg;
        if(this.cfg == null) begin
            this.cfg = new();
        end
    endfunction

    function void pre_randomize();
        if(cfg.rand_count == 0) begin
            assert(cfg.randomize());
        end else begin
            cfg.rand_count--;
        end

        this.ifg_enabled  = cfg.ifg_enabled;
        this.ifg_disabled = cfg.ifg_disabled;
        this.ifg_low      = cfg.ifg_low;
        this.ifg_high     = cfg.ifg_high;
    endfunction
endclass

class ifg_config_avst_tx extends ifg_config;
    ifg_config_rand_setup cfg;

    function new (ifg_config_rand_setup cfg = null);
        this.cfg = cfg;
        if(this.cfg == null) begin
            this.cfg = new();
        end
    endfunction

    function void pre_randomize();
        if(cfg.rand_count == 0) begin
            assert(cfg.randomize());
        end else begin
            cfg.rand_count--;
        end

        this.ifg_enabled  = cfg.ifg_enabled;
        this.ifg_disabled = cfg.ifg_disabled;
        this.ifg_low      = cfg.ifg_low;
        this.ifg_high     = cfg.ifg_high;
    endfunction
endclass

//////////////////////////////////////////////
// AVALON DRIVER
//////////////////////////////////////////////
class avalon #(DATA_WIDTH) extends base;

    //convert avalon to pcie and pcie to avalon
    pcie2avalon pcie_tx;
    avalon2pcie pcie_rx;

    //lower level drivers
    avst_rx::agent #(DATA_WIDTH/256) driver_rx;
    avst_tx::agent #(DATA_WIDTH/256) driver_tx;

    function new(string inst, sv_common_pkg::tTransMbx transMbx,
                 virtual avst_tx_if #(DATA_WIDTH/256) vif_cq,
                 virtual avst_rx_if #(DATA_WIDTH/256) vif_cc);
        super.new(inst);
        //TX
        pcie_tx = new ({inst, " TO AVALON"}, transMbx);
        driver_tx  = new({inst, " AVALON TX DRIVER"}, pcie_tx.outMbx, vif_cq);

        //RX
        pcie_rx   = new();
        driver_rx = new({inst, " AVALON RX DRIVER"}, vif_cc);
        driver_rx.setCallbacks(pcie_rx);
    endfunction

    virtual task setEnabled();
        super.setEnabled();
        pcie_tx.setEnabled();
        driver_tx.setEnabled();

        driver_rx.setEnabled();
    endtask

    virtual task setDisabled();
       super.setDisabled();
       pcie_tx.setDisabled();
       driver_tx.setEnabled();

       driver_rx.setDisabled();
    endtask

    virtual function void ifg_set(ifg_config_rand_setup rx, ifg_config_rand_setup tx);
        ifg_config_avst_rx ifg_rx;
        ifg_config_avst_tx ifg_tx;

        ifg_rx = new(rx);
        driver_rx.ifg_set(ifg_rx);

        ifg_tx = new(tx);
        pcie_tx.ifg_set(ifg_tx);
    endfunction

    virtual function void verbose_set(int unsigned level);
        //driver_rx.verbose_set(level);
        //driver_tx.verbose_set(level);
        pcie_tx.verbose_set(level);
        pcie_rx.verbose_set(level);
    endfunction

    virtual function void setPcieCQCallbacks(sv_common_pkg::DriverCbs cbs);
        pcie_tx.setCallbacks(cbs);
    endfunction

    virtual function void setPcieCCCallbacks(sv_common_pkg::MonitorCbs cbs);
        pcie_rx.setCallbacks(cbs);
    endfunction
endclass
