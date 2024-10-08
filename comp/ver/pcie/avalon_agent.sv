/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

 ///////////////////////////////////////////////////
// IFG CONGIG AVALON
///////////////////////////////////////////////////
class ifg_config_avst_rx extends avst_rx::ifg_config;
    ifg_config_setup cfg;

    function new (ifg_config_setup cfg = null);
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

class ifg_config_avst_tx extends ifg_delay;
    ifg_config_setup cfg;

    function new (ifg_config_setup cfg = null);
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


//////////////////////////////////////////////////
// AVALON driver
class avalon_agent #(RCB, MPS, DEVICE, DATA_WIDTH) extends agent #(RCB, MPS);

    localparam REGIONS = DATA_WIDTH/256;
    //translation from AVALON/AXI to PCIE
    pcie_driver_cbs   avst_tx_driver_cbs;
    avalon_rc_driver  avst_tx_driver;
    avalon_rq_monitor avst_rx_monitor;

    //AVALON agents
    avst_rx::agent #(REGIONS) rq_hw;
    avst_tx::agent #(REGIONS) rc_hw;

    function new (string inst, sv_common_pkg::tTransMbx mbx_input, virtual avst_rx_if #(REGIONS) vif_rx, virtual avst_tx_if#(REGIONS).monitor vif_tx);
        super.new(inst, mbx_input);

        //avalon RQ
        avst_rx_monitor = new({inst, " Avalon to Root"});
        avst_rx_monitor.setCallbacks(this.tags_req_cbs);
        rq_hw = new ({inst, " avalon RQ"}, vif_rx);
        rq_hw.setCallbacks(avst_rx_monitor.avalon_rq_cbs);

        //pcie to avalon
        avst_tx_driver_cbs = new(4);
        avst_tx_driver = new({inst, " Driver PCIE to AVALON"}, pcie_sq_cbs.mbx_response);
        avst_tx_driver.setCallbacks(avst_tx_driver_cbs);

        rc_hw = new ({inst, " avalon RC"}, avst_tx_driver_cbs.mbx_response, vif_tx);
    endfunction

    task setEnabled();
        super.setEnabled();
        rq_hw.setEnabled();
        avst_rx_monitor.setEnabled();
        avst_tx_driver.setEnabled();
        rc_hw.setEnabled();
    endtask

    task setDisabled();
        super.setDisabled();
        rq_hw.setDisabled();
        avst_rx_monitor.setDisabled();
        avst_tx_driver.setDisabled();
        rc_hw.setDisabled();
    endtask

    function void verbosity_set(int unsigned level);
        super.verbosity_set(level);
        avst_tx_driver.verbosity_set(level);
        avst_rx_monitor.verbosity_set(level);
        rc_hw.verbosity_set(level);
        rq_hw.verbosity_set(level);
    endfunction

    virtual function void rq_setCallbacks(sv_common_pkg::MonitorCbs cbs);
        avst_rx_monitor.setCallbacks(cbs);
    endfunction

    function void rq_ifg_set(ifg_config_setup cfg);
        ifg_config_avst_rx cfg_avst;
        cfg_avst = new(cfg);
        rq_hw.ifg_set(cfg_avst);
    endfunction

    function void rc_ifg_set(ifg_config_setup cfg);
        ifg_config_avst_tx cfg_avst;
        cfg_avst = new(cfg);
        avst_tx_driver.ifg_set(cfg_avst);
    endfunction
endclass
