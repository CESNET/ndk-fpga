/*
 * monitorCbs.sv: Monitor Callbacks
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
 *            Petr Kobiersky <kobiersky@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  /* This is a abstract class for creating objects which get benefits from
   * function callback. This object can be used with Monitor
   * class. Inheritence from this basic class is neaded for functionality.
   */
  class MonitorCbs;
  // -- Class Methods --

    // ------------------------------------------------------------------------
    // Function is called before post_rx is called (modification of transaction)
    virtual task pre_rx(ref Transaction transaction, string inst);
      // By default, callback does nothing
    endtask

    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(Transaction transaction, string inst);
      // By default, callback does nothing
    endtask

  endclass : MonitorCbs

