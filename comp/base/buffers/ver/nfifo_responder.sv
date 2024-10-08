/*
 * fifo_responder.sv: Fifo Responder
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- Fifo Responder Class
  // --------------------------------------------------------------------------
  /* This class is responsible for random intra- and intertransaction's dealys.
   * It's used by class monitor. Unit must be enabled by "setEnable()" function
   * call. Random delaying can be stoped by "setDisable()" function call.
   */
  class nFifoResponder #(int pDataWidth=64,int pFlows=2,int pBlSize=512,int pLutMem=0, pGlobSt=0);

    // -- Private Class Atributes --
    string  inst;                            // Monitor identification
    bit     enabled;                         // Monitor is enabled
    virtual iNFifoTx.nfifo_read_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) f_r;

    // ----
    rand bit enFrDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int frDelayEn_wt             = 1;
      int frDelayDisable_wt        = 3;
    rand integer frDelay; // Delay between transactions
      // Delay between transactions limits
      int frDelayLow          = 0;
      int frDelayHigh         = 3;
    // ----

    // -- Constrains --
    constraint cDelays {
      enFrDelay dist { 1'b1 := frDelayEn_wt,
                       1'b0 := frDelayDisable_wt
                     };

      frDelay inside {
                      [frDelayLow:frDelayHigh]
                     };
      }


    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iNFifoTx.nfifo_read_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) f_r
                   );
      this.enabled     = 0;           // Monitor is disabled by default
      this.f_r         = f_r;         // Store pointer interface
      this.inst        = inst;        // Store driver identifier

      // Setting default values for Fifo interface
      f_r.nfifo_read_cb.READ <= 1;     // Ready even if disabled

    endfunction

    // -- Enable Responder ------------------------------------------------------
    // Enable responder and runs responder process
    task setEnabled();
      enabled = 1; // Monitor Enabling
      fork
        run();     // Creating monitor subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled

    // -- Disable responder -----------------------------------------------------
    // Disable responder
    task setDisabled();
      enabled = 0; // Disable monitor, after receiving last transaction
      f_r.nfifo_read_cb.READ   <= 1;
    endtask : setDisabled

    // -- Run Responder ---------------------------------------------------------
    //
    task run();
      BufferTransaction transaction;
      Transaction tr;
      while (enabled) begin              // Repeat in forewer loop
        assert(randomize());
        waitFrDelay();
      end
    endtask : run

    // -- Not ready between transactions --------------------------------------
    task waitFrDelay();
      if (enFrDelay) begin
        repeat (frDelay) begin
          f_r.nfifo_read_cb.READ <= 0;
          @(f_r.nfifo_read_cb);
        end
        f_r.nfifo_read_cb.READ   <= 1;
        if (frDelay > 0) @(f_r.nfifo_read_cb);
      end
    endtask : waitFrDelay

  endclass: nFifoResponder
