/*
 * driverCbs.sv: FrameLink Driver
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
  // -- Driver Callbacks
  // --------------------------------------------------------------------------
  /* This is a abstract class for creating objects which get benefits from
   * function callback. This object can be used with Driver
   * class. Inheritence from this basic class is neaded for functionality.
   */
   class DriverCbs;

    // -- Class Methods --

    // ------------------------------------------------------------------------
    // Function is called before is transaction sended - usefull for
    // transaction modification

    virtual task pre_tx(ref Transaction transaction, string inst);
      // By default, callback does nothing
    endtask: pre_tx

    // ------------------------------------------------------------------------
    // Function is called after is transaction sended throw interface -
    // usefull for scoreboards

    virtual task post_tx(Transaction transaction, string inst);
      // By default, callback does nothing
    endtask: post_tx

  endclass : DriverCbs

