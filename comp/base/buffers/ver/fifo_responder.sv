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
  class FifoResponder #(int pDataWidth=64,int pFlows=2,int pBlSize=512,
                        int pLutMem=0,int pGlobSt=0,int pOutputReg=0);

    // -- Private Class Atributes --
    string  inst;                            // Monitor identification
    bit     enabled;                         // Monitor is enabled
    virtual iNFifoRx.fifo_read_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) f_r;

    // ----
    rand bit enFrDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int frDelayEn_wt             = 1;
      int frDelayDisable_wt        = 50;
    rand integer frDelay; // Delay between transactions
      // Delay between transactions limits
      int frDelayLow               = 0;
      int frDelayHigh              = 10;
    rand bit enPipeDelay;  // Enable/Disable PIPE_EN delays between transactions
      // Enable/Disable PIPE_EN delays between transaction (weights)
      int pipeDelayEn_wt           = 1;
      int pipeDelayDisable_wt      = 50;
    rand integer pipeDelay; // Delay between transactions
      // Delay between transactions limits
      int pipeDelayLow             = 0;
      int pipeDelayHigh            = 10;
    // ----

    // -- Constrains --
    constraint cDelays {
      enFrDelay dist { 1'b1 := frDelayEn_wt,
                       1'b0 := frDelayDisable_wt
                     };

      frDelay inside {
                      [frDelayLow:frDelayHigh]
                     };

      enPipeDelay dist { 1'b1 := pipeDelayEn_wt,
                         1'b0 := pipeDelayDisable_wt
                       };

      pipeDelay inside {
                        [pipeDelayLow:pipeDelayHigh]
                       };
      }


    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iNFifoRx.fifo_read_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) f_r
                   );
      this.enabled     = 0;           // Monitor is disabled by default
      this.f_r         = f_r;         // Store pointer interface
      this.inst        = inst;        // Store driver identifier

      // Setting default values for Fifo interface
      f_r.fifo_read_cb.READ    <= 1;     // Ready even if disabled
      f_r.fifo_read_cb.PIPE_EN <= 1;

    endfunction

    // -- Enable Responder ----------------------------------------------------
    // Enable responder and runs responder process
    task setEnabled();
      enabled = 1; // Responder Enabling
      fork
        run();     // Creating responder subprocess
        run_pipe();
      join_none;   // Don't wait for ending
    endtask : setEnabled

    // -- Disable responder ---------------------------------------------------
    // Disable responder
    task setDisabled();
      enabled = 0; // Disable responder, after receiving last transaction
      f_r.fifo_read_cb.READ    <= 1;
      f_r.fifo_read_cb.PIPE_EN <= 1;
    endtask : setDisabled

    // -- Run Responder -------------------------------------------------------
    task run();
      while (enabled) begin              // Repeat in forewer loop
        assert(randomize());
        waitFrDelay();
      end
    endtask : run

    // -- Run Responder -------------------------------------------------------
    task run_pipe();
      while (enabled) begin              // Repeat in forewer loop
        assert(randomize());
        waitPipeDelay();
      end
    endtask : run_pipe

    // -- Not ready between transactions --------------------------------------
    // Generates not ready between transactions and BLOCK_ADDR
    task waitFrDelay();
      if (enFrDelay) f_r.fifo_read_cb.READ    <= 0;
      else f_r.fifo_read_cb.READ    <= 1;

      repeat (frDelay) begin
        f_r.fifo_read_cb.BLOCK_ADDR <= $urandom_range(pFlows-1);
        @(f_r.fifo_read_cb);
      end

    endtask : waitFrDelay

    // -- Not ready between transactions --------------------------------------
    // Generates not ready between transactions and BLOCK_ADDR
    task waitPipeDelay();
      if (enPipeDelay) f_r.fifo_read_cb.PIPE_EN <= 0;
      else f_r.fifo_read_cb.PIPE_EN <= 1;

      repeat (pipeDelay) @(f_r.fifo_read_cb);

    endtask : waitPipeDelay

  endclass: FifoResponder
