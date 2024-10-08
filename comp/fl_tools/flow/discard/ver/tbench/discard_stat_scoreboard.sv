/* \file discard_stat_scoreboard.sv
 * \brief Discard Stat Scoreboard
 * \author Marek Santa <xsanta06@stud.fit.vutbr.cz>
 * \date 2010
 */
/*
 * Copyright (C) 2010 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import math_pkg::*;

  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief Frame Link Driver Callbacks
   *
   * This class is responsible adding transaction into transaction table and
   * offers possibility to modify transaction.
   *
   * \param pChannels - count of channels
   * \param behav - TransactionTable behavior
   */

  class ScoreboardDriverCbs #(int pChannels=2, int behav=TR_TABLE_FIRST_ONLY)
                                                   extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Transaction Table
    TransactionTable #(behav) sc_table[] = new [pChannels];

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    //! Constructor
    /*!
     * \param sc_table - transaction tables
     */
    function new (TransactionTable #(behav) sc_table[]);
      this.sc_table = sc_table;
    endfunction

    // -- Pre_tx --------------------------------------------------------------
    //! Pre_tx
    /*!
     * Function is called before transaction is sended. It modifies transaction
     * in way first two bytes of deader sets to header size, second two bytes
     * sets to payload size.
     *
     * \param transaction - transaction
     */
    virtual task pre_tx(ref Transaction transaction, string inst);
      FrameLinkTransaction tr;
      logic[15:0] segmentSize;
      logic[15:0] hardwareSize;

      $cast(tr, transaction);

      // Create FL NetCOPE transaction format
      // Compute sizes
      segmentSize  = tr.data[0].size + tr.data[1].size;
      hardwareSize = tr.data[0].size - 4;

      // Set sizes in frame header
      tr.data[0][0] = segmentSize[ 7:0];
      tr.data[0][1] = segmentSize[15:8];
      tr.data[0][2] = hardwareSize[ 7:0];
      tr.data[0][3] = hardwareSize[15:8];

    endtask

    // -- Post_tx -------------------------------------------------------------
    //! Post_tx
    /*!
     * Function is called after transaction is sended. It adds transaction into
     * correct transaction table - depends on witch driver sends transaction
     *
     * \param transaction - transaction
     * \param inst - driver identifier
     */

    virtual task post_tx(Transaction transaction, string inst);
       // Gets number of transaction table from instance name
       int i;
       string driverLabel;

       for(i=0; i < pChannels; i++) begin
         driverLabel = $sformatf( "Driver %0d", i);
         if (driverLabel == inst) break;
       end

       sc_table[i].add(transaction);
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief Frame Link Monitor Callbacks
   *
   * This class is responsible removing transaction from transaction table.
   *
   * \param pChannels - count of channels
   * \param behav - TransactionTable behavior
   */

  class ScoreboardMonitorCbs #(int pChannels=2, int behav=TR_TABLE_FIRST_ONLY)
                                                   extends MonitorCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Scoreboard identification
    string inst;
    //! Transaction Table
    TransactionTable #(behav) sc_table[] = new[pChannels];

    // -- Constructor ---------------------------------------------------------
    //! Constructor
    /*!
     * \param sc_table - transaction tables
     * \param inst - scoreboard identification
     */
    function new (TransactionTable #(behav) sc_table[], string inst="");
      this.sc_table = sc_table;
      this.inst     = inst;
    endfunction

    // -- Post_rx -------------------------------------------------------------
    //! Post_tx
    /*!
     * Function is called after transaction is received. It checks correct
     * transaction table for the same transaction. If they match, transaction is
     * removed, otherwise error is reporting.
     *
     * \param transaction - transaction
     * \param inst - monitor identifier
     */

    virtual task post_rx(Transaction transaction, string inst);
      bit status=0;
      // Gets number of transaction table from instance name
      int i;
      string monitorLabel;
      string tableLabel;

      for(i=0; i< pChannels; i++) begin
        monitorLabel = $sformatf("Monitor %0d", i);
        if (monitorLabel == inst) break;
      end

      tableLabel = $sformatf("%s %0d", this.inst, i);

      sc_table[i].remove(transaction, status);
      if (status==0)begin
         $write("Unknown transaction received from monitor %d\n", inst);
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         transaction.display();
         sc_table[i].display(.inst(tableLabel));
         $stop;
      end;
    endtask

  endclass : ScoreboardMonitorCbs


  // --------------------------------------------------------------------------
  // -- Discard Stat Scoreboard
  // --------------------------------------------------------------------------
  /*!
   * \brief Discard Stat Scoreboard
   *
   * This class is responsible for creating Tranaction table and monitor and
   * driver callback classes. It also prints Transaction table.
   *
   * \param pChannels - count of channels
   * \param behav - TransactionTable behavior
   */
  class DiscardStatScoreboard #(int pChannels=2, int behav=TR_TABLE_FIRST_ONLY);
    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Scoreboard identification
    string inst;

    //! Transaction Table
    TransactionTable     #(behav)         scoreTable[] = new[pChannels];
    //! Monitor callback
    ScoreboardMonitorCbs #(pChannels, behav) monitorCbs;
    //! Driver callback
    ScoreboardDriverCbs  #(pChannels, behav) driverCbs;

    // -- Constructor ---------------------------------------------------------
    //! Constructor
    /*!
     * It creates monitor and driver callbacks and Transaction Table for each
     * flow.
     *
     * \param inst - scoreboard identification
     */
    function new (string inst="");
      this.inst = inst;

      for(int i=0;i<pChannels;i++)
        this.scoreTable[i]= new;

      this.monitorCbs = new(scoreTable, inst);
      this.driverCbs  = new(scoreTable);
    endfunction

    // -- Display -------------------------------------------------------------
    //! Display
    /*!
     * It prints Transaction Table
     *
     */
    task display();
      for (int i=0; i<pChannels; i++) begin
        string tableLabel;
        tableLabel = {tableLabel, $sformatf(" %0d",  i)};
        scoreTable[i].display(.inst(tableLabel));
      end
    endtask

  endclass : DiscardStatScoreboard

