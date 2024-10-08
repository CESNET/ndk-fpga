/*
 * scoreboard.sv: Frame Link Scoreboard
 * Copyright (C) 2007 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_fl_pkg::*;

  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs #(int pInputCount = 1) extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(0) sc_table;
    int pktCnt[pInputCount] = '{default: 0};

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new (TransactionTable #(0) sc_table);
      this.sc_table = sc_table;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called before is transaction sended
    // Allow modify transaction before is sended
    virtual task pre_tx(ref Transaction transaction, string inst);
    //   FrameLinkTransaction tr;
    //   $cast(tr,transaction);

    // Example - set first byte of first packet in each frame to zero
    //   tr.data[0][0]=0;
    endtask

    // ------------------------------------------------------------------------
    // Function is called after is transaction sended

    virtual task post_tx(Transaction transaction, string inst);
      for(int i=0; i< pInputCount; i++) begin
        string driverLabel;
        driverLabel = $sformatf("Driver %0d", i);
        if (driverLabel == inst) begin
          pktCnt[i]++;
          break;
        end
      end

      sc_table.add(transaction);
    endtask

    // ------------------------------------------------------------------------
    // Function displays number of packet received on each interface
    function void display;
      $write("-----------------------------------------------\n");
      $write("Number of packets transmited on each interface:\n");
      for(int i=0; i < pInputCount; i++)
        $write("Interface %0d: %0d pkts\n",i,pktCnt[i]);
      $write("-----------------------------------------------\n");
    endfunction: display

  endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs extends MonitorCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(0) sc_table;

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new (TransactionTable #(0) sc_table);
      this.sc_table = sc_table;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)

    virtual task post_rx(Transaction transaction, string inst);
      bit status=0;
      // transaction.display("MONITOR");
      sc_table.remove(transaction, status);
      if (status==0)begin
         $write("Unknown transaction received from monitor %d\n", inst);
         transaction.display();
         sc_table.display();
         $stop;
       end;
    endtask

  endclass : ScoreboardMonitorCbs

  // -- Constructor ---------------------------------------------------------
  // Create a class
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard #(int pInputCount = 1);
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable    #(0)           scoreTable;
    ScoreboardMonitorCbs               monitorCbs;
    ScoreboardDriverCbs #(pInputCount) driverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new ();
      this.scoreTable = new;
      this.monitorCbs = new(scoreTable);
      this.driverCbs  = new(scoreTable);
    endfunction

    // -- Display -------------------------------------------------------------
    // Create a class
    task display();
      driverCbs.display();
      scoreTable.display();
    endtask

  endclass : Scoreboard

