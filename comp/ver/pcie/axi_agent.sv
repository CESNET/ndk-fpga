/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/
class AxiResponder #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH) extends sv_axi_pkg::Axi4SResponder #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH);

    ifg_config_setup ifg_cfg;

    function new(string i, virtual iAxi4STx#(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH).tb v);
        super.new(i, v);
        ifg_cfg = new();
    endfunction

    function void ifg_set(ifg_config_setup cfg);
        ifg_cfg = cfg;
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

class AxiDriver #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, RC_ST_COUNT) extends sv_axi_pcie_pkg::Axi4S_RC_agent#(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, RC_ST_COUNT);

    ifg_config_setup ifg_cfg;

    function new(string inst, tTransMbx transMbx, virtual iAxi4SRx#(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH).tb v);
        super.new(inst, transMbx, v);
        ifg_cfg = new();
    endfunction

    function void ifg_set(ifg_config_setup cfg);
        ifg_cfg = cfg;
    endfunction

    function void pre_randomize();
        if(ifg_cfg.rand_count == 0) begin
            assert(ifg_cfg.randomize());
        end else begin
            ifg_cfg.rand_count--;
        end

        this.ifgEnable_wt  = ifg_cfg.ifg_enabled;
        this.ifgDisable_wt = ifg_cfg.ifg_disabled;
        this.ifgLow        = ifg_cfg.ifg_low;
        this.ifgHigh       = ifg_cfg.ifg_high;
    endfunction
endclass
//////////////////////////////////////////////////
// AVALON driver
class axi_agent #(RCB, MPS, DEVICE, DATA_WIDTH) extends agent #(RCB, MPS);

    localparam RQ_TUSER_WIDTH = (DEVICE=="7SERIES") ? 60 : (DEVICE=="ULTRASCALE" && DATA_WIDTH == 512) ? 137 : 62;
    localparam RC_TUSER_WIDTH = (DEVICE=="7SERIES") ? 75 : (DEVICE=="ULTRASCALE" && DATA_WIDTH == 512) ? 161 : 75;
    localparam RQ_ST_COUNT    = (DEVICE=="7SERIES") ? 1  : (DEVICE=="ULTRASCALE" && DATA_WIDTH == 512) ? 2   : 1;
    localparam RC_ST_COUNT    = (DEVICE=="7SERIES") ? 2  : (DEVICE=="ULTRASCALE" && DATA_WIDTH == 512) ? 4   : 2;

    //Transaction from AXI to PCIE
    axi_rq_monitor  rq_monitor;
    pcie_driver_cbs rc_driver_cbs;
    axi_rc_driver   rc_driver;

    //AXI AGENTS
    sv_axi_pcie_pkg::Axi4S_RQ_agent #(DATA_WIDTH, RQ_TUSER_WIDTH, 32, RQ_ST_COUNT) axiRQ;
    AxiResponder  #(DATA_WIDTH, RQ_TUSER_WIDTH, 32)              axiRQ_responder;
    AxiDriver     #(DATA_WIDTH, RC_TUSER_WIDTH, 32, RC_ST_COUNT) axiRC;
    string inst;

    function new (string inst, sv_common_pkg::tTransMbx mbx_input, virtual iAxi4STx  #(DATA_WIDTH, RQ_TUSER_WIDTH, 32) vif_rx, virtual iAxi4SRx  #(DATA_WIDTH, RC_TUSER_WIDTH, 32) vif_tx);
        super.new(inst, mbx_input);

        //Request modules
        rq_monitor = new();
        rq_monitor.setCallbacks(this.tags_req_cbs);
        axiRQ = new({inst, "AXI Request "}, vif_rx);
        axiRQ.setCallbacks(rq_monitor.axi_rq_cbs);
        axiRQ_responder = new({inst, " AXI Responder"}, vif_rx);

        //Response modules
        rc_driver_cbs = new(4);
        rc_driver     = new({inst, " PCIE TO AXI DRIVER"}, pcie_sq_cbs.mbx_response);
        rc_driver.setCallbacks(rc_driver_cbs);
        axiRC = new({inst, " AXI Response agent"}, rc_driver_cbs.mbx_response, vif_tx);
    endfunction

    task setEnabled();
        axiRQ.setEnabled();
        rq_monitor.setEnabled();
        super.setEnabled();
        axiRQ_responder.setEnabled();
        rc_driver.setEnabled();
        axiRC.setEnabled();
    endtask

    task setDisabled();
        axiRQ.setDisabled();
        rq_monitor.setDisabled();
        super.setDisabled();
        axiRQ_responder.setDisabled();
        rc_driver.setDisabled();
        axiRC.setDisabled();
    endtask

    function void verbosity_set(int unsigned level);
        super.verbosity_set(level);
        rq_monitor.verbosity_set(level);
        rc_driver.verbosity_set(level);
    endfunction

    virtual function void rq_setCallbacks(sv_common_pkg::MonitorCbs cbs);
        rq_monitor.setCallbacks(cbs);
    endfunction

    function void rq_ifg_set(ifg_config_setup cfg);
        axiRQ_responder.ifg_set(cfg);
    endfunction

    function void rc_ifg_set(ifg_config_setup cfg);
        axiRC.ifg_set(cfg);
    endfunction

endclass
