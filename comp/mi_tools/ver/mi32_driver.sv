/*
 * mi32_driver.sv: Mi32 Driver
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
 *            Petr Kastovsky <kastovsky@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- Mi32 Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to Mi32
   * interface. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transaction by calling "sendTransaction" function.
   */
  class Mi32Driver;

    // -- Private Class Atributes --
    bit       busy;                             // Indication of the "busy" state
    string    inst;                             // Driver identification
    bit       enabled;                          // Driver is enabled
    tTransMbx transMbx;                         // Transaction mailbox
    DriverCbs cbs[$];                           // Callbacks list
    virtual iMi32.tb    mi;

    rand bit enTxDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int txDelayEn_wt             = 1;
      int txDelayDisable_wt        = 3;

    rand integer txDelay; // Delay between transactions
      // Delay between transactions limits
      int txDelayLow          = 0;
      int txDelayHigh         = 3;
    // ----

    // -- Constrains --
    constraint cDelays {
      enTxDelay dist { 1'b1 := txDelayEn_wt,
                       1'b0 := txDelayDisable_wt
                     };

      txDelay inside {
                      [txDelayLow:txDelayHigh]
                     };
      }

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object
    function new ( string inst,
                   tTransMbx transMbx,
                   virtual iMi32.tb mi
                         );
      this.enabled     = 0;            // Driver is disabled by default
      this.mi          = mi;           // Store pointer interface
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier
      this.busy        = 0;            // Driver is not busy by default

      this.mi.cb.ADDR      <= 0;
      this.mi.cb.DWR       <= 0;
      this.mi.cb.BE        <= 0;
      this.mi.cb.RD        <= 0;
      this.mi.cb.WR        <= 0;
    endfunction: new


    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List
    function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks

    // -- Enable Driver -------------------------------------------------------
    // Enable driver and runs driver process
    task setEnabled();
      enabled = 1; // Driver Enabling
      fork
        run();     // Creating driver subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled

    // -- Disable Driver ------------------------------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable driver, after sending last transaction it ends
    endtask : setDisabled

    // -- Send Transaction ----------------------------------------------------
    // Send transaction to mi32 interface
    task sendTransaction( Mi32Transaction transaction );
      Transaction tr;
      $cast(tr, transaction);

      busy = 1;
      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(tr, inst);

      // Wait before sending transaction
      if (enTxDelay) repeat (txDelay) @(mi.cb);

      // Send transaction
      executeTransaction(transaction);

      // Set no request
      mi.cb.RD     <= 0;
      mi.cb.WR     <= 0;

      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(tr, inst);
      busy = 0;
    endtask : sendTransaction

    // -- Private Class Methods --

    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      Mi32Transaction transaction;
      Transaction to;
      @(mi.cb);                        // Wait for clock
      while (enabled) begin            // Repeat while enabled
        transMbx.get(to);              // Get transaction from mailbox
        $cast(transaction,to);
        assert(randomize());
        sendTransaction(transaction);  // Send Transaction
//        transaction.display();
      end
    endtask : run


    // -- Wait for ARDY -----------------------------------------------------
    // Wait for address ready signal
    task waitForARDY();
      while (mi.cb.ARDY == 0) begin
        @(mi.cb);
      end;
    endtask : waitForARDY

    // -- Execute transaction -----------------------------------------------
    // Send transaction command and data
    task executeTransaction(Mi32Transaction tr);

      // Allign data from transaction to fl.DATA
      mi.cb.ADDR      <= tr.address;
      mi.cb.DWR       <= tr.data;
      mi.cb.BE        <= tr.be;
      mi.cb.WR        <= tr.rw;  // wr == 1 => write request
      mi.cb.RD        <= !tr.rw; // wr == 0 => read request

      @(mi.cb);
      waitForARDY();  // Wait until oposit side set ready

      // clear pending request signals
      mi.cb.WR        <= 0;
      mi.cb.RD        <= 0;

    endtask : executeTransaction

  endclass : Mi32Driver

