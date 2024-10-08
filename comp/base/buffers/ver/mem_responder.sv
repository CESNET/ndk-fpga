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
  class MemResponder #(int pDataWidth=64,int pFlows=2,int pBlSize=512,int pLutMem=0, pGlobSt=0);

    // -- Private Class Atributes --
    string  inst;                            // Monitor identification
    bit     enabled;                         // Monitor is enabled
    virtual iNFifoRx.mem_read_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) m_r;

    int rd_addr[] = new [pFlows];            // Store RD_ADDR for each FLOW
    mailbox #(int) dontRead;

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

    rand bit enPipeDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int pipeDelayEn_wt             = 1;
      int pipeDelayDisable_wt        = 3;
    rand integer pipeDelay; // Delay between transactions
      // Delay between transactions limits
      int pipeDelayLow          = 0;
      int pipeDelayHigh         = 3;


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
                   virtual iNFifoRx.mem_read_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) m_r
                   );
      this.enabled     = 0;           // Monitor is disabled by default
      this.m_r         = m_r;         // Store pointer interface
      this.inst        = inst;        // Store driver identifier

      dontRead = new;

      // Setting default values for Fifo interface
      m_r.mem_read_cb.READ <= 1;     // Ready even if disabled
      m_r.mem_read_cb.PIPE_EN <= 1;
    endfunction

    // -- Enable Responder ------------------------------------------------------
    // Enable responder and runs responder process
    task setEnabled();
      enabled = 1; // Monitor Enabling
      fork
        run1();     // Creating responder subprocess
        run2();     // Creating responder subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled

    // -- Disable responder -----------------------------------------------------
    // Disable responder
    task setDisabled();
      enabled = 0; // Disable monitor, after receiving last transaction
      m_r.mem_read_cb.READ   <= 1;
      m_r.mem_read_cb.PIPE_EN <= 1;
    endtask : setDisabled

    // -- Run Responder ---------------------------------------------------------
    task run1();
      while (enabled) begin              // Repeat in forewer loop
        assert(randomize());
        waitFrDelay();
      end
    endtask : run1

    // -- Run Responder ---------------------------------------------------------
    task run2();
      while (enabled) begin              // Repeat in forewer loop
        assert(randomize());
        waitPipeDelay();
      end
    endtask : run2

    // -- Not ready between transactions --------------------------------------
    task waitFrDelay();
      int block;
      int dont;

      if (enFrDelay) begin
        m_r.mem_read_cb.READ <= 0;
        repeat (frDelay) begin
          @(m_r.mem_read_cb);
        end
      end
      else begin
        m_r.mem_read_cb.READ   <= 1;
        if (m_r.mem_read_cb.REL_LEN_DV!=0) m_r.mem_read_cb.READ   <= 0;
        if (dontRead.num()!=0) begin
          dontRead.get(dont);
          if (dont)begin
            m_r.mem_read_cb.READ   <= 0;
            $write("DontREAD was correctly read\n");
          end
        end
        @(m_r.mem_read_cb);
      end

    endtask : waitFrDelay

    // -- Not ready between transactions --------------------------------------
    task waitPipeDelay();
      if (enPipeDelay) begin
        m_r.mem_read_cb.PIPE_EN <= 0;
        repeat (pipeDelay) @(m_r.mem_read_cb);
      end
      else begin
        m_r.mem_read_cb.PIPE_EN   <= 1;
        if (m_r.mem_read_cb.REL_LEN_DV!=0) m_r.mem_read_cb.PIPE_EN   <= 0;
        @(m_r.mem_read_cb);
      end

    endtask : waitPipeDelay

  endclass: MemResponder
