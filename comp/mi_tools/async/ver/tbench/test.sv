/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;
import test_pkg::*;
import sv_mi_common_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
    output logic       MASTER_RESET,
    output logic       SLAVE_RESET,
    input  logic       MASTER_CLK,
    input  logic       SLAVE_CLK,
    iMi                MASTER,
    iMi                SLAVE
    );

    // --------------------------------------------------------------------------
    //                       Variables declaration
    // --------------------------------------------------------------------------
    //! MI32 Master
    Generator                   master_gen;
    sv_mi_pkg::MiAgentMaster  #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH)  master_agent;
    sv_mi_pkg::MiCover        #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH)  master_cov;
    Generator                   slave_gen;
    sv_mi_pkg::MiAgentSlave   #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH)  slave_agent;
    sv_mi_pkg::MiCover        #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH)  slave_cov;

    scoreboard #(MI_WIDTH, MI_META_WIDTH) sc;
    // --------------------------------------------------------------------------
    //                       Creating Environment tasks
    // --------------------------------------------------------------------------
    task createEnvironment();
        sv_mi_pkg::rand_mi_responder_delay  slave_rand_ardy;
        sv_mi_pkg::rand_mi_responder_delay  slave_rand_drdy;
        sv_mi_pkg::rand_mi_driver_delay master_rand_rdy;

        // Create scoreboard
        sc = new();

        // MASTER
        master_gen   = new ("MI Generator", 0);
        master_rand_rdy = new();
        master_agent = new ("MI Master Agent", master_gen.transMbx, MASTER);
        master_agent.driver.delay = master_rand_rdy;
        master_agent.monitor.setCallbacks(sc.master);
        master_cov  = new ("MI Master Cover", MASTER, 16);

        // SLAVE
        slave_gen   = new ("MI Generator", 0);
        slave_rand_ardy = new();
        slave_rand_drdy = new();
        slave_agent = new ("MI Master Agent", slave_gen.transMbx, SLAVE);
        slave_agent.responder.rand_ardy = slave_rand_ardy;
        slave_agent.responder.rand_drdy = slave_rand_drdy;
        slave_agent.monitor.setCallbacks(sc.slave);
        slave_cov  = new ("MI Slave Cover", SLAVE, 16);
    endtask : createEnvironment

    // --------------------------------------------------------------------------
    //                       SETUP TEST => add blueprint
    // --------------------------------------------------------------------------
    function setup_test();
        sv_mi_pkg::mi_sequence #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH) master_tr;
        //sv_mi_pkg::MiTransaction #(MI_WIDTH) master_tr;
        sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH) slave_tr;

        master_tr = new();
        master_gen.blueprint = master_tr;

        slave_tr = new();
        slave_gen.blueprint = slave_tr;
    endfunction

    // -- Reset Design ----------------------------------------------------------
    task resetDesign();
        MASTER_RESET=1;                       // Init Reset variable
        SLAVE_RESET=1;
        #RESET_TIME     MASTER_RESET = 0;     // Deactivate reset after reset_time
        SLAVE_RESET = 0;
    endtask : resetDesign

    // -- Enable Test Environment -----------------------------------------------
    task enableTestEnvironment();
        // Enable drivers
        master_agent.setEnabled();

        // Enable monitors
        slave_agent.setEnabled();
    endtask : enableTestEnvironment

    // -- Disable Test Environment ----------------------------------------------
    task disableTestEnvironment();
         // Enable drivers
        master_agent.setDisabled();

        // Enable monitors
        slave_agent.setDisabled();
    endtask

    // --------------------------------------------------------------------------
    //                            Test cases
    // --------------------------------------------------------------------------
    // -- Test Case 1 -----------------------------------------------------------
    task test1();
      $write("\n\n############ TEST CASE 1 ############\n\n");
      // Enable Test environment
      setup_test();

      enableTestEnvironment();
      resetDesign(); // Reset design


      // Run MI Generator
      master_gen.setEnabled(TRANSACTION_COUNT);
      slave_gen.setEnabled();

      // While MI32 Generator is active do nothing
      wait (master_gen.enabled == 0);
      #(1000ns);

      // Disable Test Enviroment
      disableTestEnvironment();

      // Display Scoreboard
      sc.display();
      master_cov.display();
      slave_cov.display();
    endtask: test1

    // --------------------------------------------------------------------------
    //                           Main test part
    // --------------------------------------------------------------------------
    initial begin
      // -------------------------------------
      // DESIGN ENVIROMENT
      // -------------------------------------
      createEnvironment(); // Create Test Enviroment
      // -------------------------------------
      // TESTING
      // -------------------------------------
      test1();       // Run Test 1

      // -------------------------------------
      // STOP TESTING
      // -------------------------------------
      $write("Verification finished successfully!\n");
      $stop();       // Stop testing
    end

endprogram

