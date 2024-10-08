/*
 * generator.sv: Generator class package
 * Copyright (C) 2007 CESNET
 * Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
 *            Petr Kobiersky  <kobiersky@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- Generator Class
  // --------------------------------------------------------------------------
  class Generator;

    // -- Public Class Atributes --

    //-------------------------------------------------------------------------
    /*
     * Internal mailbox is used only when no mailbox is specified in the
     * constructor.
     */
    tTransMbx transMbx;

    //-------------------------------------------------------------------------
    /*
     * The generator will stop after the specified number of object
     * instances has been generated and consumed by the output channel.
     * The generator must be reset before it can be restarted. If the
     * value of this property is 0, the generator will not stop on
     * its own.
     */
    int unsigned stop_after_n_insts = 0;

    //-------------------------------------------------------------------------
    /*
     * Transaction or data descriptor instance that is repeatedly
     * randomized to create the random content of the output descriptor
     * stream. The individual instances of the output stream are copied
     * from this instance, after randomization, using the
     * Transaction::copy() method. stream_id property of this instance is
     * set to the generator’s stream identifier before each randomization.
     * The Transaction::data_id property of this instance is also set
     * before each randomization. It will be reset to 0 when the generator
     * is reset and after the specified maximum number of instances has
     * been generated.
     */
    Transaction blueprint;

    bit enabled;

    // -- Protected Class Atributes
    protected int stream_id;

    protected int scenario_id;

    protected int data_id;


    // -- Public Class Methods

    //-------------------------------------------------------------------------
    /*
     * Creates a new instance of the generator class with the specified
     * instance name and optional stream identifier. The generator can
     * be optionally connected to the specified output channel(mailbox).
     * If no output channel instance is specified, one will be created
     * internally in the out_chan property.
     */
    function new(string inst, int stream_id = -1, tTransMbx transMbx = null);
      if (transMbx == null)
        // NOTE: since we have drivers that can start multiple transactions at the same time, we need to have big enough stack of ready transactions in the mailbox, 100 should be enough for all cases
        this.transMbx = new(100);        // Create own mailbox
      else
        this.transMbx = transMbx;        // Use created mailbox

      enabled         = 0;               // Disable generator by default
      blueprint       = null;            // Null the blueprint transaction
      stream_id       = stream_id;       // Set stream id
      scenario_id     = -1;              // Set default scenario
      data_id         = 0;               // Set default data identifier
    endfunction : new

    //-------------------------------------------------------------------------
    /*
     * Enable generator for creating n Instances.
     */
    task setEnabled(int unsigned nInst=32'hFFFFFFFF);
      enabled = 1;
      stop_after_n_insts = nInst;
      data_id = 0;
      fork
        run();
      join_none;
    endtask : setEnabled

    //-------------------------------------------------------------------------
    /*
     * Disable generator immediately.
     */
    task setDisabled();
      this.enabled = 0;
      wait (transMbx.num() == 0);
    endtask : setDisabled


    //-------------------------------------------------------------------------
    virtual task run();
      Transaction trans;
      if ( blueprint != null) begin
        // While is enabled or stop = 0 or number of generated transactions not exceed limit
        while (enabled && (data_id < stop_after_n_insts || stop_after_n_insts == 0)) begin
          trans = blueprint.copy;               // Copy from blueprint
          trans.stream_id    = stream_id;       // Set stream id
          trans.scenario_id  = -1;              // Set default scenario
          trans.data_id      = data_id;         // Set instance count
          assert(trans.randomize);              // Randomize transaction
          transMbx.put(trans);                  // Put transaction to mailbox
          data_id=data_id+1;                    // Increment instance counter
        end;
      end else begin
        $write("The blueprint transaction in generator must be set\n");
      end

      wait (transMbx.num() == 0);
      enabled = 0;
    endtask : run

  endclass : Generator

