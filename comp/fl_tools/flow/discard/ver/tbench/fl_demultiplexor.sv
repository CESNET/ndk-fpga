/*
 * fl_demultiplexor.sv: FrameLink Demultiplexor
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
  // -- Frame Link Demultiplexor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for reading signals from FrameLink
   * interface. Transactions are received from input interface and
   * demultiplexed to output interfaces.
   */
  class FrameLinkDemultiplexor #(int pDataWidth=32, int pDremWidth=2,
                                 int pChannels=2, int pStatusWidth=16);

    // -- Private Class Atransibutes --
    bit    enabled = 0;
    string inst;
    int unsigned channel;
    virtual iFrameLinkTx.tb #(pDataWidth, pDremWidth) tx;
    virtual iFrameLinkRx.tb #(pDataWidth, pDremWidth) rx[pChannels];
    virtual iDiscardStat.tx_tb #(pChannels, pStatusWidth) chan;

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object
    function new ( string inst,
                   virtual iFrameLinkTx.tb #(pDataWidth,pDremWidth) tx,
                   virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) rx[],
                   virtual iDiscardStat.tx_tb #(pChannels, pStatusWidth) chan
                         );
      this.inst        = inst;
      this.tx          = tx;         // Store pointer interface
      this.rx          = rx;         // Store pointer interface
      this.chan        = chan;       // Store pointer interface

      for (int i=0; i<pChannels; i++) begin
        this.rx[i].cb.DATA           <= 0;
        this.rx[i].cb.DREM           <= 0;
        this.rx[i].cb.SOF_N          <= 1;
        this.rx[i].cb.EOF_N          <= 1;
        this.rx[i].cb.SOP_N          <= 1;
        this.rx[i].cb.EOP_N          <= 1;
        this.rx[i].cb.SRC_RDY_N      <= 1;
      end
    endfunction: new

    // -- Enable Demultiplexor -----------------------------------------------
    // Enable demultiplexor and runs demultiplexor process
    task setEnabled();
      enabled = 1; // Demultiplexor Enabling
      fork
        run();     // Creating demultiplexor subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled

    // -- Disable Multipexor --------------------------------------------------
    // Disable demultiplexor
    task setDisabled();
      enabled = 0; //Disable demultiplexor
    endtask : setDisabled

    // -- Private Class Methods --

    // -- Run Demultiplexor ---------------------------------------------------
    // According to channel demultiplex signals form input interface to
    // respective output interface
    task run();
      int unsigned channel;
      @(tx.cb);                        // Wait for clock

      while (enabled) begin            // Repeat while enabled
        for (int i=0; i<pChannels; i++)
          rx[i].cb.SRC_RDY_N <= 1;

        channel = chan.tx_cb.TX_CHAN;
        rx[channel].cb.DATA      <= tx.cb.DATA;
        rx[channel].cb.DREM      <= tx.cb.DREM;
        rx[channel].cb.SOF_N     <= tx.cb.SOF_N;
        rx[channel].cb.EOF_N     <= tx.cb.EOF_N;
        rx[channel].cb.SOP_N     <= tx.cb.SOP_N;
        rx[channel].cb.EOP_N     <= tx.cb.EOP_N;
        rx[channel].cb.SRC_RDY_N <= tx.cb.SRC_RDY_N;
        @(tx.cb);
      end
    endtask : run

  endclass : FrameLinkDemultiplexor

