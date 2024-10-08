/*
 * test.sv mtc verification enviromet
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

import test_pkg::*;

`include "watch_dog.sv"

program TEST (
	input  logic  CLK,
	output logic  RESET,

    i_pcie_c      PCIE_C,
	iMi           MI
);




    sv_common_pkg::Generator                 slave_gen;
    sv_mi_pkg::MiAgentSlave     #(MI_WIDTH, MI_WIDTH) slave_agent;
    //sv_mi_pkg::MiCover        #(MI_WIDTH, MI_WIDTH) slave_cov;

    //pcie2mi
    sv_common_pkg::Generator                                pcie_gen;
    pcie2mi::root               #(DEVICE, PCIE_DATA_WIDTH)  pcie_c;

    //scoreboard
    scoreboard::sc #(32) model;
    watch_dog            watch;

    function void createEnv();
        //MI RAND DRIVER
        sv_mi_pkg::rand_mi_responder_delay  slave_rand_ardy;
        sv_mi_pkg::rand_mi_responder_delay  slave_rand_drdy;
        //PCIE RAND DRIVER
        pcie2mi::ifg_config_rand_setup pcie_ifg_rx;
        pcie2mi::ifg_config_rand_setup pcie_ifg_tx;

        //MI SLAVE
        slave_rand_ardy = new();
        slave_rand_drdy = new();
        slave_gen   = new("MI SLAVE GEN");
        slave_agent = new("MI SLAVE AGENT", slave_gen.transMbx, MI);
        slave_agent.responder.rand_ardy = slave_rand_ardy;
        slave_agent.responder.rand_drdy = slave_rand_drdy;

        // PCIE
        pcie_gen = new("PCIE GEN");
        pcie_c = new("PCIE2MI ", pcie_gen.transMbx, PCIE_C);
        pcie_c.verbose_set(VERBOSE);
        pcie_ifg_rx = new();
        pcie_ifg_rx.enable_min  = 0;
        pcie_ifg_rx.enable_max  = 10;
        pcie_ifg_rx.disable_min = 0;
        pcie_ifg_rx.disable_max = 100;
        pcie_ifg_tx = new();
        pcie_ifg_tx.enable_min  = 0;
        pcie_ifg_tx.enable_max  = 1;
        pcie_ifg_tx.disable_min = 0;
        pcie_ifg_tx.disable_max = 100;
        pcie_c.ifg_set(pcie_ifg_rx, pcie_ifg_tx);

        //scoreboard
        model  = new();
        model.verbose_set(VERBOSE);
        pcie_c.setPcieCQCallbacks(model.pcie_cq_cbs);
        slave_agent.monitor.setCallbacks(model.mi_cbs);
        pcie_c.setPcieCCCallbacks(model.pcie_cc_cbs);

        //WATCH DOG
        watch = new(60us);
        pcie_c.setPcieCQCallbacks(watch.pcie_cbs);
        slave_agent.monitor.setCallbacks(watch.mi_cbs);
    endfunction

    function void setupEnv();
        sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH) mi_blueprint;
        pcie2mi::seq_cfg             pcie_tr_cfg;
        pcie2mi::seq                 pcie_tr;

        mi_blueprint = new();
        slave_gen.blueprint = mi_blueprint;

        pcie_tr_cfg = new(MRRS);
        pcie_tr     = new(pcie_tr_cfg);
        $cast(pcie_gen.blueprint, pcie_tr);
    endfunction

    task setEnabled();
        watch.setEnabled();
        slave_gen.setEnabled();
        //slave_cov.setEnabled();
        slave_agent.setEnabled();
        pcie_c.setEnabled();
        pcie_gen.setEnabled();
    endtask

    task setDisabled();
        pcie_gen.setDisabled();
        model.wait_done();
        pcie_c.setDisabled();
        slave_gen.setDisabled();
        slave_agent.setDisabled();
        watch.setDisabled();
    endtask


    task test1();
        setupEnv();
        setEnabled();

        ///////////////
        // RESET
        RESET = 1;
        #(CLK_PERIOD*40);
        RESET = 0;

        #(SIMULATION_DURATION);
        setDisabled();
        model.display("VERIFICATION SUCCESS");
    endtask

	// --------------------------------------------------------------------------
	//                           Main test part
	// --------------------------------------------------------------------------
	initial begin
        createEnv();
        test1();
		$stop();
	end

endprogram

