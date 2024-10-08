/*!
 * \file pcd_driver.sv
 * \brief Driver for PACODAG interface
 * \author Marek Santa <xsanta06@stud.fit.vutbr.cz>
 * \date 2009
 */
 /*
 * Copyright (C) 2009 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO: Driver does not check SOP signal.
 *       Driver does not clear RDY signal.
 *
 */


  // --------------------------------------------------------------------------
  // -- PACODAG Driver
  // --------------------------------------------------------------------------

  /*!
   * \brief PACODAG Driver
   *
   * This class is responsible for generating signals to PACODAG interface.
   * Transactions are received by 'transMbx' (Mailbox) property. Unit must be
   * enabled by "setEnable()" function call. Generation can be stoped by
   * "setDisable()" function call. You can send your custom transaction by
   * calling "sendTransaction" function.
   */
  class PacodagDriver #(int pDataWidth = 64) extends Driver;

    // -- Private Class Attribute --
    //! Virtual interface PACODAG
    virtual iPacodag.tb #(pDataWidth) pcd;
    // Buffer for incomming STAT_DVs
    semaphore statDvBuffer;

    // ----
    //! Enable/Disable delays inside transaction
    rand bit enInsideDelay;
      //! Enable/Disable delays inside transaction (weights)
      int insideDelayEn_wt       = 1;
      int insideDelayDisable_wt  = 3;

    //! Delay inside transaction
    rand int insideDelay;
      //! Delay inside transaction limits
      int insideDelayLow         = 0;
      int insideDelayHigh        = 3;
    // ----

    int decrement = 0;
    int increment = 0;

    //! Constrains
    constraint cInsideDelays {
      enInsideDelay dist { 1'b1 := insideDelayEn_wt,
                           1'b0 := insideDelayDisable_wt
                     };

      insideDelay inside {
                          [insideDelayLow:insideDelayHigh]
                     };
      }


    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor
    /*!
     * Creates driver object and sets default values of PACODAG interface
     * signals
     */
    function new ( string inst,
                   tTransMbx transMbx,
                   virtual iPacodag.tb #(pDataWidth)  pcd
                   );

      super.new(inst, transMbx);   // Call parent constructor

      this.pcd   = pcd;            // Store pointer interface

      this.statDvBuffer = new();

      // Setting default values for PACODAG interface
      this.pcd.cb.SRC_RDY_N    <= 1;
      this.pcd.cb.SOP_N        <= 1;
      this.pcd.cb.EOP_N        <= 1;
      this.pcd.cb.RDY          <= 1;
    endfunction: new

    // ------------------------------------------------------------------------
    //! Enable Driver
    /*!
     * Enable Driver and runs Driver process
     */
    virtual task setEnabled();
      enabled = 1; // Driver Enabling
      fork
         run();                // Creating driver subprocess
         checkStatDv();
      join_none;               // Don't wait for ending
    endtask : setEnabled

    // ------------------------------------------------------------------------
    //! Send Transaction
    /*
     * Send transaction to PACODAG interface
     * \param transaction - transaction
     */
    virtual task sendTransaction( Transaction transaction );
      PacodagTransaction tr;

      // Driver is sending transaction
      busy = 1;

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(transaction, inst);

      // Wait for SOP
//      waitForSop();

      // Wait for STAT_DV
      waitForStatDv();

      // Clear RDY
//      pcd.cb.RDY <= 0;

      // Wait before sending transaction
      if (enDelay) repeat (delay) @(pcd.cb);

      // Send transaction
      $cast(tr, transaction);
      sendData(tr);

      // Set RDY and SRC_RDY_N
//      pcd.cb.RDY       <= 1;
      pcd.cb.SRC_RDY_N <= 1;

      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(transaction, inst);

      // Driver is not sending transaction
      busy = 0;
    endtask : sendTransaction

    // -- Private Class Methods --

    // ------------------------------------------------------------------------
    //! Run Pacodag Driver
    /*!
     * Take transactions from mailbox and send them to interface
     */
    virtual task run();
      Transaction transaction;

      // Wait for clock
      @(pcd.cb);

      while (enabled) begin            // Repeat while enabled
        // Randomize rand variables
        assert(randomize());

        // Get transaction from mailbox
        transMbx.get(transaction);

        // Send Transaction
        sendTransaction(transaction);

//        transaction.display(inst);
      end
    endtask : run

    // ------------------------------------------------------------------------
    //! Check STAT_DV
    /*!
     * Check if STAT_DV arrives and add it into buffer
     */
    task checkStatDv();
      // Wait for clock
      @(pcd.cb);

      while (enabled) begin            // Repeat while enabled
        // If STAT_DV "add" it into buffer
        if (pcd.cb.STAT_DV) begin
           statDvBuffer.put();
           //$write("Inkrementace %d\n", increment++);
        end
        @(pcd.cb);
      end
    endtask : checkStatDv

    // ------------------------------------------------------------------------
    //! Send data
    /*!
     * Send PACODAG transaction data
     */
    task sendData(PacodagTransaction tr);
      int m = 0;
      logic[pDataWidth-1:0] dataToSend = 0;

      // -- For all parts --
      for (int i=0; i < tr.partCount; i++) begin

        // -- For all bytes in part --
        for (int j=0; j < tr.data[i].size; j++) begin

          // -- Set SOP_N
          if (j<pDataWidth/8) begin
            pcd.cb.SOP_N <= 0;                      //Set Start of Part
          end

          // Set one Data Byte
          for (int k=0; k < 8; k++)
            dataToSend[m++] = tr.data[i][j][k];


          // Last Byte in Part
          if (j==tr.data[i].size-1) begin          //Last byte of part
            pcd.cb.EOP_N <= 0;                        //Set End Of Part

            // Set REM signal
            if (tr.data[i].size%(pDataWidth/8) == 0)
              pcd.cb.REM <= (pDataWidth/8)-1;
            else
              pcd.cb.REM <= (tr.data[i].size%(pDataWidth/8))-1;

            m=pDataWidth;
          end

          // When data word is ready to send
          if (m==pDataWidth) begin
            pcd.cb.DATA <= dataToSend;
            randomWait();     // Create not ready
            @(pcd.cb);        // Send data
            waitForAccept();  // Wait until oposit side set ready

            // Init for sending next data word
            pcd.cb.SOP_N <= 1;
            pcd.cb.EOP_N <= 1;
            dataToSend = 0;
            m=0;
          end

        end
      end

    endtask : sendData

    // ------------------------------------------------------------------------
    //! Wait for SOP
    /*!
     * Wait until SOP arrives
     */
    task waitForSop();
      while (!pcd.cb.SOP)
        @(pcd.cb);
    endtask : waitForSop

    // ------------------------------------------------------------------------
    //! Wait for STAT_DV
    /*!
     * Wait until there is some STAT_DV in buffer
     */
    task waitForStatDv();
      while (!statDvBuffer.try_get())
        @(pcd.cb);

        //$write("Dekrementace %d\n", decrement++);
    endtask : waitForStatDv

    // ------------------------------------------------------------------------
    //! Wait for accept
    /*!
     * Wait for accepting of general bits word of transaction
     */
    task waitForAccept();
      while (pcd.cb.DST_RDY_N) begin
        @(pcd.cb);
      end;
    endtask : waitForAccept

    // ------------------------------------------------------------------------
    //! Random wait
    /*!
     * Random wait during sending transaction (Set SRC_RDY_N to 1)
     */
    task randomWait();
      if (enInsideDelay)
        repeat (insideDelay) begin
          pcd.cb.SRC_RDY_N <= 1;
          @(pcd.cb); // Wait for send
        end
      pcd.cb.SRC_RDY_N <= 0;
      assert(randomize());     // Randomize variables for next randomWait
    endtask : randomWait

  endclass : PacodagDriver
