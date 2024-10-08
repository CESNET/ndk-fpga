/*
 * fl_multiplexor.sv: FrameLink Multiplexor
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
  // -- Frame Link Multiplexor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to FrameLink
   * interface. Transactions are received from input interfaces and
   * multiplexed to output interface.
   */
  class FrameLinkMultiplexor #(int pDataWidth=32, int pDremWidth=2,
                               int pChannels=2, int pStatusWidth=16);

    // -- Private Class Atransibutes --
    bit    enabled = 0;
    string inst;
    rand int unsigned channel;
    virtual iFrameLinkTx.tb #(pDataWidth, pDremWidth) tx[pChannels];
    virtual iFrameLinkRx.tb #(pDataWidth, pDremWidth) rx;
    virtual iDiscardStat.rx_tb #(pChannels, pStatusWidth) chan;

    // ----
    rand int muxDelay; // Delay between multiplexing
      // Delay between multiplexing limits
      int muxDelayLow          = 1;
      int muxDelayHigh         = 3;
    // ----

    // -- Constrains --
    constraint cDelays {
      channel < pChannels;

      muxDelay inside {
                       [muxDelayLow:muxDelayHigh]
                      };
      }


    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object
    function new ( string inst,
                   virtual iFrameLinkTx.tb #(pDataWidth,pDremWidth) tx[],
                   virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) rx,
                   virtual iDiscardStat.rx_tb #(pChannels, pStatusWidth) chan
                         );
      this.inst        = inst;
      this.tx          = tx;         // Store pointer interface
      this.rx          = rx;         // Store pointer interface
      this.chan        = chan;       // Store pointer interface

      this.rx.cb.DATA           <= 0;
      this.rx.cb.DREM           <= 0;
      this.rx.cb.SOF_N          <= 1;
      this.rx.cb.EOF_N          <= 1;
      this.rx.cb.SOP_N          <= 1;
      this.rx.cb.EOP_N          <= 1;
      this.rx.cb.SRC_RDY_N      <= 1;
      this.chan.rx_cb.RX_CHAN   <= 0;
    endfunction: new

    // -- Enable Multiplexor --------------------------------------------------
    // Enable multiplexor and runs multiplexor process
    task setEnabled();
      enabled = 1; // Multiplexor Enabling
      fork
        run();     // Creating multiplexor subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled

    // -- Disable Multipexor --------------------------------------------------
    // Disable multiplexor
    task setDisabled();
      enabled = 0; //Disable multiplexor, after sending last transaction it ends
    endtask : setDisabled

    // -- Private Class Methods --

    // -- Run Multiplexor -----------------------------------------------------
    // Randomly generate channel and multiplex signals from respective input
    // interface to output interface
    task run();
      int unsigned prevChannel;
      @(rx.cb);                        // Wait for clock

      while (enabled) begin            // Repeat while enabled
        prevChannel = channel;
        assert(randomize());           // Randomize rand variables

        for (int i=0; i<pChannels; i++)
          tx[i].cb.DST_RDY_N <= 1;

        rx.cb.SRC_RDY_N <= 1;
        repeat (muxDelay) begin
          rx.cb.DATA      <= tx[prevChannel].cb.DATA;
          rx.cb.DREM      <= tx[prevChannel].cb.DREM;
          rx.cb.SOF_N     <= tx[prevChannel].cb.SOF_N;
          rx.cb.EOF_N     <= tx[prevChannel].cb.EOF_N;
          rx.cb.SOP_N     <= tx[prevChannel].cb.SOP_N;
          rx.cb.EOP_N     <= tx[prevChannel].cb.EOP_N;
          rx.cb.SRC_RDY_N <= tx[prevChannel].cb.SRC_RDY_N;
          tx[channel].cb.DST_RDY_N <= 0;
          chan.rx_cb.RX_CHAN       <= prevChannel;
          prevChannel = channel;
          @(rx.cb);
          rx.cb.SRC_RDY_N <= 1;
        end
      end
    endtask : run

  endclass : FrameLinkMultiplexor

