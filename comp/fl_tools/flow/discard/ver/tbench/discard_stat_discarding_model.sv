/*
 * discard_stat_discarding_model.sv: Discarding Model for Discard Stat
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

  import math_pkg::*;

  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class DiscardStatDriverCbs #(int pChannels=2) extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    DriverCbs cbs[$];                          // Callbacks list
    bit discardFlag[pChannels] = '{default: 0};
    longint unsigned droppedFrames[pChannels] = '{default: 0};
    longint unsigned passedFrames[pChannels]  = '{default: 0};
    longint unsigned droppedLength[pChannels] = '{default: 0};
    longint unsigned passedLength[pChannels]  = '{default: 0};

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new();
    endfunction

    // ------------------------------------------------------------------------
    // Function is called before is transaction sended
    virtual task pre_tx(ref Transaction transaction, string inst);
       cbs[0].pre_tx(transaction, inst);
    endtask

    // ------------------------------------------------------------------------
    // Function is called after is transaction sended
    virtual task post_tx(Transaction transaction, string inst);
       // Gets number of transaction table from instance name
       int i;
       string driverLabel;
       FrameLinkTransaction tr;

       $cast(tr, transaction);

       for(i=0; i < pChannels; i++) begin
         driverLabel = $sformatf("Driver %0d", i);
         if (driverLabel == inst) break;
       end

       if (discardFlag[i]) begin
         discardFlag[i] = 0;
         droppedFrames[i]++;
         droppedLength[i] += tr.data[0].size+tr.data[1].size;
       end
       else begin
         cbs[0].post_tx(transaction, inst);
         passedFrames[i]++;
         passedLength[i] += tr.data[0].size+tr.data[1].size;
       end
    endtask

    // ------------------------------------------------------------------------
    // Function sets flag to discard actual frame
    function void setDiscardFlag(int channel);
       discardFlag[channel] = 1;
    endfunction

    // ------------------------------------------------------------------------
    // Get frames statistics
    function void getStats(output longint unsigned df[], pf[], dl[], pl[]);
       df = droppedFrames;
       pf = passedFrames;
       dl = droppedLength;
       pl = passedLength;
    endfunction

   endclass : DiscardStatDriverCbs

  // --------------------------------------------------------------------------
  // -- Frame Link Discarding Model Class
  // --------------------------------------------------------------------------
  /* This class is responsible for prediction of packet discarding. Unit must
   * be enabled by "setEnable()" function call. Monitoring can be stoped by
   * "setDisable()" function call.
   */
  class DiscardStatDiscardingModel #(int pDataWidth=32, pDremWidth=2,
                                     pChannels=2, pStatusWidth=16,
                                     pOutputReg=0);

    // -- Private Class Atributes --
    string    inst;                            // Checker identification
    bit       enabled;                         // Checker is enabled
    bit discardFlag[pChannels] = '{default: 0};
    DiscardStatDriverCbs #(pChannels) discardStatCbs;
    virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) rx;
    virtual iDiscardStat.rx_tb #(pChannels,pStatusWidth) chan;
    virtual iDiscardStat.stat_tb #(pChannels,pStatusWidth) stat;

    rand bit incrementStatus;

    // -- Constrains --
    constraint cIncrement {
      incrementStatus dist { 1'b1 := 100,
                             1'b0 := 1
                           };
    }

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) rx,
                   virtual iDiscardStat.rx_tb #(pChannels,pStatusWidth) chan,
                   virtual iDiscardStat.stat_tb #(pChannels,pStatusWidth) stat
                   );
      this.enabled     = 0;           // Model is disabled by default
      this.rx          = rx;          // Store pointer interface
      this.chan        = chan;        // Store pointer interface
      this.stat        = stat;        // Store pointer interface
      this.inst        = inst;        // Store driver identifier
      this.discardStatCbs   = new();

    endfunction

    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List
    function void setCallbacks(DriverCbs cbs);
      discardStatCbs.cbs.push_back(cbs);
    endfunction : setCallbacks

    // -- Enable Model --------------------------------------------------------
    // Enable model and runs model's process
    task setEnabled();
      enabled = 1; // Model Enabling
      fork
        run();     // Creating model subprocess
        setStatus();     // Creating model subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled

    // -- Disable Model -------------------------------------------------------
    // Disable checker
    task setDisabled();
      enabled = 0; // Disable model
    endtask : setDisabled

    // -- Run Model -----------------------------------------------------------
    // Predict packet discarding
    task run();
      int unsigned channel;
      logic[pStatusWidth-1:0] status;
      logic[pChannels*pStatusWidth-1:0] wholeStatus;
      logic[pStatusWidth-1:0] statusMask = '1;
      logic[15:0]             packetSize;
      int unsigned            maxStatus = 1<<(pStatusWidth+log2(pDataWidth/8)-1);
      int unsigned            statusPlusPacketSize;

      $write("maxStatus:%0x\n",maxStatus);

      while (enabled) begin                   // Repeat in forever loop
        // Wait for Start of Frame
        waitForSOFandGetStatus(wholeStatus);

        channel = chan.rx_cb.RX_CHAN;
        status = (wholeStatus >> (channel*pStatusWidth)) & statusMask;

        packetSize = rx.cb.DATA[15:0];
//        $write("whole Status: %x\n",wholeStatus);
        $write("Channel: %0d Status(words): %4h Status: %4h packetSize: %4h\n",
                channel,status,status*pDataWidth/8,packetSize);

        statusPlusPacketSize = status*pDataWidth/8+packetSize+pDataWidth/8;

        // If pOutputReg is true, there is one more cycle delay so we need to
        // add one more word
        if (pOutputReg) statusPlusPacketSize += pDataWidth/8;

        if (statusPlusPacketSize > maxStatus) begin
          // There is no space for packet
          discardStatCbs.setDiscardFlag(channel);
          discardFlag[channel] = 1;
          $write("discarding\n");
        end
        else
          discardFlag[channel] = 0;

        wholeStatus = stat.stat_cb.STATUS;
        @(rx.cb);
      end
    endtask : run

    // -- Wait for SOF -------------------------------------------------------
    // Wait for Start of Frame
    task waitForSOFandGetStatus(inout logic[pChannels*pStatusWidth-1:0]
                                                                 wholeStatus);
      while (rx.cb.SOF_N || rx.cb.SRC_RDY_N || rx.cb.DST_RDY_N) begin
        wholeStatus = stat.stat_cb.STATUS;
        @(rx.cb);
      end
    endtask : waitForSOFandGetStatus

    // -- Set STATUS ---------------------------------------------------------
    // Randomize and set STATUS
    task setStatus();
      logic[pStatusWidth-1:0] status[pChannels] = '{default:0};
      logic[pChannels*pStatusWidth-1:0] wholeStatus  = 0;
      int unsigned maxStatus = 1<<(pStatusWidth-1);

      @(stat.stat_cb);

      while (enabled) begin
        assert(randomize());

        // increment status for one flow
        if (incrementStatus) begin
          if (discardFlag[chan.rx_cb.RX_CHAN]==0 && !rx.cb.SRC_RDY_N &&
              status[chan.rx_cb.RX_CHAN]<maxStatus)
            status[chan.rx_cb.RX_CHAN]++;
        end
        // decrement status for one flow
        else begin
          logic[pStatusWidth-1:0] newStatus = 0;
          newStatus = $urandom_range(status[chan.rx_cb.RX_CHAN]);
//          $write("status decrementing for %0d: %0x @%0t\n",chan.rx_cb.RX_CHAN,
//          newStatus, $time);
          status[chan.rx_cb.RX_CHAN] = newStatus;
        end

        // set STATUS
        for (int i=pChannels-1; i>=0; i--) begin
          wholeStatus <<= pStatusWidth;
          wholeStatus += status[i];
        end
        stat.stat_cb.STATUS <= wholeStatus;
        @(stat.stat_cb);
      end
    endtask : setStatus

    // -- Get Stats -----------------------------------------------------------
    // Get frames statistics
    function void getStats(output longint unsigned df[], pf[], dl[], pl[]);
      discardStatCbs.getStats(df,pf,dl,pl);
    endfunction

endclass : DiscardStatDiscardingModel
