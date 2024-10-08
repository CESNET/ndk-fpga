/*
 * base.sv base class for pcie
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

////////////////////////////////////////////
// extends Axi4_CQ driver
////////////////////////////////////////////
class AxiCQDriver #(AXI_DATA_WIDTH, AXI_CCUSER_WIDTH) extends sv_axi_pkg::Axi4SDriver #(AXI_DATA_WIDTH, AXI_CCUSER_WIDTH, 32);
    ifg_config_rand_setup ifg_cfg;

    function new(string inst, sv_common_pkg::tTransMbx transMbx, virtual iAxi4SRx#(AXI_DATA_WIDTH, AXI_CCUSER_WIDTH, 32).tb v);
        super.new(inst, transMbx, v);
        ifg_cfg = new();
    endfunction

    virtual task invalidateWordData();
        super.invalidateWordData();
        vif.cb.TUSER <= 'x;
    endtask

    function void pre_randomize();
        if(ifg_cfg.rand_count == 0) begin
            assert(ifg_cfg.randomize());
        end else begin
            ifg_cfg.rand_count--;
        end

        this.txDelayEn_wt      = ifg_cfg.ifg_enabled;
        this.txDelayDisable_wt = ifg_cfg.ifg_disabled;
        this.txDelayLow        = ifg_cfg.ifg_low;
        this.txDelayHigh       = ifg_cfg.ifg_high;
    endfunction

    function void ifg_set(ifg_config_rand_setup ifg);
        this.ifg_cfg = ifg;
    endfunction

    virtual task exposeWordData(sv_axi_pkg::AxiTransaction tr, int cycle, inout finished);
        sv_axi_pkg::AxiTransaction cq;

        logic[AXI_CCUSER_WIDTH-1:0] data = 'x;

        $cast(cq, tr);
        super.exposeWordData(tr, cycle, finished);

        data[80] = 1'b0;
        if (cycle == 0) begin
            data[3:0] = cq.fbe;
            data[11:8] = cq.lbe;
            data[80] = 1'b1;
        end

        if (finished) begin
        end

        vif.cb.TUSER <= data;
    endtask
endclass

////////////////////////////////////////////
// extends Axi4_CC responder
////////////////////////////////////////////
class AxiCCResponder #(AXI_DATA_WIDTH, AXI_CC_USER_WIDTH) extends sv_axi_pkg::Axi4SResponder  #(AXI_DATA_WIDTH, AXI_CC_USER_WIDTH, 32);
    ifg_config_rand_setup ifg_cfg;

    function new(string i, virtual iAxi4STx#(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH).tb v);
        super.new(i, v);
        ifg_cfg = new();
    endfunction

    function void ifg_set(ifg_config_rand_setup ifg);
        this.ifg_cfg = ifg;
    endfunction

    function void pre_randomize();
        if(ifg_cfg.rand_count == 0) begin
            assert(ifg_cfg.randomize());
        end else begin
            ifg_cfg.rand_count--;
        end

        this.wordDelayEnable_wt  = ifg_cfg.ifg_enabled;
        this.wordDelayDisable_wt = ifg_cfg.ifg_disabled;
        this.wordDelayLow        = ifg_cfg.ifg_low;
        this.wordDelayHigh       = ifg_cfg.ifg_high;
    endfunction

endclass

//////////////////////////////////////////////
//// Convert pcie_CQ to axi_CQ
//////////////////////////////////////////////
class pcie2Axi  extends pcie2common#(8);

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

    function void gen_header(output byte unsigned headerArray[16], input logic [5:0] barap, logic [2:0] bar, logic [7:0] func,
                             logic [7:0] tag, logic [15:0] requester, logic [3:0] reqType, logic [10:0] length, logic [63:2] addr);
        logic [127:0] header;

        header = '0;
        header[1:0]    = 2'b0; //Addres type
        header[63:2]   = addr;
        header[74:64]  = length;
        header[78:75]  = reqType;
        header[95:80]  = requester;
        header[103:96] = tag;
        header[111:104] = func;
        header[114:112] = bar;   //bar
        header[120:115] = barap; //bar aperature

       {<<byte{headerArray}} = header;
    endfunction

    task run();
        PcieRequest tr_in;
        sv_axi_pkg::AxiTransaction  tr_out;

        while (enabled) begin
            byte unsigned headerArray[16];
            byte unsigned data[];

            getTr(tr_in);
            if (verbose > 0) begin
                tr_in.display({inst, " GET PCIE CQ TRANSACTION"});
            end

            //change tr_in to axi
            tr_out = new();
            tr_out.lbe = tr_in.lbe;
            tr_out.fbe = tr_in.fbe;

            gen_header(headerArray, 6'd24, 0, 8'h7, tr_in.tag, 0, (tr_in.type_tr == PCIE_RQ_READ ? 0 : 1), tr_in.length, tr_in.addr);
            if (tr_in.data.size() != 0) begin
                data = { <<32 { { <<8 {tr_in.data}}}};
            end else begin
                data = {};
            end
            tr_out.data = {headerArray, data};

            if (verbose > 1) begin
                tr_out.display({inst, " SEND AXI CQ TRANSACTION"});
            end
            outMbx.put(tr_out);
            foreach (cbs[i]) begin
                cbs[i].post_tx(tr_in, inst);
            end
        end
    endtask
endclass

//////////////////////////////////////////////
//// Convert axi_CC to pcie_CQ
//////////////////////////////////////////////
class Axi2pcie  extends sv_common_pkg::MonitorCbs;
    sv_common_pkg::MonitorCbs cbs[$];
    int unsigned verbose;

    function new();
        this.verbose  = 0;
    endfunction

    function void verbose_set(int unsigned level);
        this.verbose = level;
    endfunction

    function void setCallbacks(sv_common_pkg::MonitorCbs cbs);
        this.cbs.push_back(cbs);
    endfunction

    virtual task pre_rx(ref sv_common_pkg::Transaction transaction, string inst);
    endtask

    virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
        PcieCompletion compl;

        sv_axi_pkg::AxiTransaction #(32) tr;
        logic [96-1:0] header;
        logic [6:0]  addr;
        int unsigned tag;
        int unsigned dword_count;
        int unsigned byte_count;

        $cast(tr, transaction);
        header = { <<32 {tr.data[0:2]}};
        tag    = header[71:64];
        dword_count = header[42:32];
        byte_count  = header[28:16];
        addr        = header[6:0];


        if (verbose > 1) begin
            tr.display("AXI CC TRANSACTION: ");
            $write("\ttag %d\n\tdword count %d\n\tbyte_count %d\n\taddr %h\n", tag, dword_count, byte_count, addr);
        end

        if (dword_count != tr.data.size()-3) begin
            tr.display("DWORD COUNT DOESN'T MATCH DATA SIZE");
            $write("\ttag %d\n\tdword count %d\n\tbyte_count %d\n\taddr %h\n", tag, dword_count, byte_count, addr);
            $error("DWORD COUNT DOESN'T MATCH DATA SIZE dword_count %d +3 != data.size() %d\n", dword_count, tr.data.size());
            $stop();
        end

        compl = new();
        compl.data = new[dword_count];
        for (int it = 0; it < dword_count; it++) begin
            compl.data[it] = tr.data[3 + it];
        end
        compl.byte_count    = byte_count;
        compl.lower_address = addr;
        compl.dword_count   = dword_count;
        compl.tag           = tag;

        if (verbose > 0) begin
            compl.display("PCIE CC TRANSACTION");
        end
        foreach (cbs[i]) begin
            cbs[i].post_rx(compl, inst);
        end
    endtask
endclass

//////////////////////////////////////////////
// AXI DRIVER
//////////////////////////////////////////////
class axi #(AXI_DATA_WIDTH, AXI_CQ_USER_WIDTH, AXI_CC_USER_WIDTH) extends base;

    //convert axi to pcie and back
    pcie2Axi   axi_gen;
    Axi2pcie   pcieCbs;

    //CQ
    AxiCQDriver #(AXI_DATA_WIDTH, AXI_CQ_USER_WIDTH) axi_driver;
    //CC
    sv_axi_pkg::Axi4SMonitor    #(AXI_DATA_WIDTH, AXI_CC_USER_WIDTH, 32) axiCC;
    AxiCCResponder              #(AXI_DATA_WIDTH, AXI_CC_USER_WIDTH)     axiCCResponder;


    function new(string inst, sv_common_pkg::tTransMbx transMbx,
                 virtual iAxi4SRx #(AXI_DATA_WIDTH, AXI_CQ_USER_WIDTH, 32).tb vif_cq,
                 virtual iAxi4STx #(AXI_DATA_WIDTH, AXI_CC_USER_WIDTH, 32)    vif_cc);

        super.new(inst);
        axi_gen    = new({inst, "PCIE2AXI "}, transMbx);
        //CQ
        axi_driver = new({inst, "AXI "}, axi_gen.outMbx, vif_cq);
        //CC
        axiCC          = new("MI2PCIE MONITOR",   vif_cc);
        axiCCResponder = new("MI2PCIE RESPONDER", vif_cc);

        //Callbacks
        pcieCbs        = new();
        axiCC.setCallbacks(pcieCbs);
    endfunction

    virtual task setEnabled();
        //CC
        axiCC.setEnabled();
        axiCCResponder.setEnabled();
        //CQ
        axi_gen.setEnabled();
        axi_driver.setEnabled();
        super.setEnabled();
    endtask

    virtual task setDisabled();
        super.setDisabled();
        axi_gen.setDisabled();
        axi_driver.setDisabled();

        axiCC.setDisabled();
        axiCCResponder.setDisabled();
    endtask

    virtual function void ifg_set(ifg_config_rand_setup rx, ifg_config_rand_setup tx);
        axi_driver.ifg_set(tx);
        axiCCResponder.ifg_set(rx);
    endfunction

    virtual function void verbose_set(int unsigned level);
        axi_gen.verbose_set(level);
        pcieCbs.verbose_set(level);
    endfunction

    virtual function void setPcieCQCallbacks(sv_common_pkg::DriverCbs cbs);
        axi_gen.setCallbacks(cbs);
    endfunction

    virtual function void setPcieCCCallbacks(sv_common_pkg::MonitorCbs cbs);
        pcieCbs.setCallbacks(cbs);
    endfunction
endclass
