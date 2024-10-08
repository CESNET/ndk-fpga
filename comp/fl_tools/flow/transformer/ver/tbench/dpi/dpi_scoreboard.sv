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
  import dpi_scoreboard_pkg::*;

  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs extends DriverCbs;

    // ------------------------------------------------------------------------
    // Function is called after is transaction sended
    virtual task post_tx(Transaction transaction, string inst);
      tFlTransactionInfo info;
      FrameLinkTransaction tr;
      int last;
      $cast(tr, transaction);

      info.stream_id   = tr.stream_id;
      info.scenario_id = tr.scenario_id;
      info.data_id     = tr.data_id;
      info.inst        = inst;
      for (int i=0; i < tr.packetCount; i++) begin
        last = (i==tr.packetCount-1);
        assert(c_flPostTx(info,last,tr.data[i]));
      end
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs extends MonitorCbs;

    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(Transaction transaction, string inst);
      tFlTransactionInfo info;
      FrameLinkTransaction tr;
      int last;
      $cast(tr, transaction);

      info.stream_id   = tr.stream_id;
      info.scenario_id = tr.scenario_id;
      info.data_id     = tr.data_id;
      info.inst        = inst;
      for (int i=0; i < tr.packetCount; i++) begin
        last = (i==tr.packetCount-1);
        assert(c_flPostRx(info,last,tr.data[i]));
      end
    endtask


  endclass : ScoreboardMonitorCbs

  // -- Constructor ---------------------------------------------------------
  // Create a class
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    ScoreboardMonitorCbs monitorCbs;
    ScoreboardDriverCbs  driverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new ();
      this.monitorCbs = new;
      this.driverCbs  = new;
    endfunction

     // -- Display -------------------------------------------------------------
    // Create a class
    task display();
      c_display();
    endtask

  endclass : Scoreboard

