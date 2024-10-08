/*!
 * \file monitor.sv
 * \brief Monitor class
 * \author Marek Santa <santa@liberouter.org>
 * \date 2010
 */
 /*
 * Copyright (C) 2010 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */


  // --------------------------------------------------------------------------
  // -- Monitor Class
  // --------------------------------------------------------------------------

  /*!
   * \brief Monitor
   *
   * This class is parent class for any Monitor. It is responsible for
   * creating transaction objects. Unit must be enabled by "setEnable()"
   * function call. Monitoring can be stoped by "setDisable()" function call.
   */
  class Monitor;

    // -- Public Class Atributes --
    //! Monitor identification
    string    inst;
    //! Monitor enabling
    bit       enabled;
    //! Monitor is sending transaction
    bit       busy;
    //! Callback list
    MonitorCbs cbs[$];


    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor
    /*!
     * Creates monitor object
     */
    function new ( string inst );

      this.enabled     = 0;            // Monitor is disabled by default
      this.busy        = 0;            // Monitor is not busy by default
      this.inst        = inst;         // Store monitor identifier

    endfunction: new

    // ------------------------------------------------------------------------
    //! Enable Monitor
    /*!
     * Enable Monitor and runs Monitor process
     */
    virtual task setEnabled();
      enabled = 1; // Monitor Enabling
      fork
         run();                // Creating monitor subprocess
      join_none;               // Don't wait for ending
    endtask : setEnabled

    // ------------------------------------------------------------------------
    //! Disable Monitor
    virtual task setDisabled();
      enabled = 0; // Disable Monitor
    endtask : setDisabled

    // ------------------------------------------------------------------------
    //! Set Callback
    /*!
     * Put callback object into List
     */
    virtual function void setCallbacks(MonitorCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks

    // ------------------------------------------------------------------------
    //! Receive Transaction
    /*
     * Receive transaction from interface
     * \param transaction - transaction
     */
    task receiveTransaction( Transaction transaction );
      assert (0)
        $fatal("Monitor: Task receiveTransaction must be implemented in derived class");
    endtask : receiveTransaction

    // -- Private Class Methods --

    // ------------------------------------------------------------------------
    //! Run Monitor
    /*!
     * Receive transactions and send them for processing by call back
     */
    virtual task run();
      assert (0)
        $fatal("Monitor: Task run must be implemented in derived class");
    endtask : run

  endclass : Monitor
