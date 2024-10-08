  /*
 * mi32_monitor.sv: Mi32 Monitor
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- Mi32 Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from Mi32
   * interface signals. After is transaction received it is sended by callback
   * to processing units (typicaly scoreboard) Unit must be enabled by
   * "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call. You can receive your custom transaction by calling
   * "receiveTransaction" function.
   */
  class Mi32Monitor extends Monitor;

    // -- Private Class Atributes --
    virtual iMi32.tb    mi;

    rand bit enRxDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int rxDelayEn_wt             = 1;
      int rxDelayDisable_wt        = 3;

    rand integer rxDelay; // Delay between transactions
      // Delay between transactions limits
      int rxDelayLow          = 0;
      int rxDelayHigh         = 3;
    // ----

    // -- Constrains --
    constraint cDelays {
      enRxDelay dist { 1'b1 := rxDelayEn_wt,
                       1'b0 := rxDelayDisable_wt
                     };

      rxDelay inside {
                      [rxDelayLow:rxDelayHigh]
                     };
      }

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create monitor object
    function new ( string inst,
                   virtual iMi32.tb mi
                         );
      super.new(inst);

      this.mi          = mi;           // Store pointer interface

      this.mi.cb.ADDR      <= 0;
      this.mi.cb.DWR       <= 0;
      this.mi.cb.BE        <= 0;
      this.mi.cb.RD        <= 0;
      this.mi.cb.WR        <= 0;
    endfunction: new

    // -- Receive Transaction -----------------------------------------------
    // Receive transaction from mi32 interface
    task receiveTransaction(Transaction tr);
      Mi32Transaction transaction;
      $cast(transaction, tr);

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_rx(tr, inst);

      // Wait before sending transaction
      if (enRxDelay) repeat (rxDelay) @(mi.cb);

      // Send transaction
      executeTransaction(transaction);

      // Set no request
      mi.cb.RD     <= 0;
      mi.cb.WR     <= 0;

      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_rx(tr, inst);
    endtask : receiveTransaction

    // -- Wait for ARDY -----------------------------------------------------
    // Wait for address ready signal
    task waitForARDY();
      while (mi.cb.ARDY == 0) begin
        @(mi.cb);
      end;
    endtask : waitForARDY

    // -- Wait for DRDY -----------------------------------------------------
    // Wait for data ready signal
    task waitForDRDY();
      while (mi.cb.DRDY == 0) begin
        @(mi.cb);
      end;
    endtask : waitForDRDY

    // -- Execute transaction -----------------------------------------------
    // Send transaction command and receive data
    task executeTransaction(Mi32Transaction tr);

      // Allign data from transaction to fl.DATA
      mi.cb.ADDR      <= tr.address;
      mi.cb.BE        <= tr.be;
      mi.cb.WR        <= tr.rw;  // wr == 1 => write request
      mi.cb.RD        <= !tr.rw; // wr == 0 => read request

      @(mi.cb);
      waitForARDY();  // Wait until oposit side set ready

      // clear pending request signals
      mi.cb.WR        <= 0;
      mi.cb.RD        <= 0;

      waitForDRDY();  // Wait until oposit side set data ready

      tr.data = mi.cb.DRD;   // Store received data

    endtask : executeTransaction

  endclass : Mi32Monitor

