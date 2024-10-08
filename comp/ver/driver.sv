/*!
 * \file driver.sv
 * \brief Driver class
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
 */


  // --------------------------------------------------------------------------
  // -- Driver Class
  // --------------------------------------------------------------------------

  /*!
   * \brief Driver
   *
   * This class is parent class for any driver. Transactions are received by
   * 'transMbx' (Mailbox) property. Unit must be enabled by "setEnable()"
   * function call. Generation can be stoped by "setDisable()" function call.
   * You can send your custom transaction by calling "sendTransaction" function.
   */
  class Driver;

    // -- Public Class Atributes --
    //! Driver identification
    string    inst;
    //! Driver enabling
    bit       enabled;
    //! Driver is sending transaction
    bit       busy;
    //! Transaction input mailbox
    tTransMbx transMbx;
    //! Callback list
    DriverCbs cbs[$];

    // ----
    //! Enable/Disable delays between transactions
    rand bit enDelay;
      //! Enable/Disable delays between transaction (weights)
      int delayEn_wt             = 1;
      int delayDisable_wt        = 3;

    //! Delay between transactions
    rand int delay;
      //! Delay between transactions limits
      int delayLow          = 0;
      int delayHigh         = 3;
    // ----

    //! Constrains
    constraint cDelays {
      enDelay dist { 1'b1 := delayEn_wt,
                     1'b0 := delayDisable_wt
                   };

      delay inside {
                    [delayLow:delayHigh]
                   };
      }


    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor
    /*!
     * Creates driver object
     */
    function new ( string inst, tTransMbx transMbx );

      this.enabled     = 0;            // Driver is disabled by default
      this.busy        = 0;            // Driver is not busy by default
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier

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
      join_none;               // Don't wait for ending
    endtask : setEnabled

    // ------------------------------------------------------------------------
    //! Disable Driver
    virtual task setDisabled();
      enabled = 0; // Disable Driver
    endtask : setDisabled

    // ------------------------------------------------------------------------
    //! Set Callback
    /*!
     * Put callback object into List
     */
    virtual function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks

    // ------------------------------------------------------------------------
    //! Send Transaction
    /*
     * Send transaction to interface
     * \param transaction - transaction
     */
    task sendTransaction( Transaction transaction );
    endtask : sendTransaction

    // -- Private Class Methods --

    // ------------------------------------------------------------------------
    //! Run Driver
    /*!
     * Take transactions from mailbox and send it to interface
     */
    virtual task run();
    endtask : run

  endclass : Driver
