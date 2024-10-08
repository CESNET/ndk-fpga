/*
 * transaction.sv: Transaction class package
 * Copyright (C) 2007 CESNET
 * Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
  // -- Transaction Class
  // --------------------------------------------------------------------------
  class Transaction;

    // -- Public Class Atributes --

    //-------------------------------------------------------------------------
     /*
     * Unique identifiers for a data model or transaction descriptor
     * instance. They specify the offset of the descriptor within a sequence and
     * the sequence offset within a stream. These properties must be set by the
     * transactor that instantiates the descriptor. They are set by the predefined
     * generator before randomization so they can be used to specify conditional
     * constraints to express instance-specific or stream-specific constraints.
     */
    int stream_id;
    int scenario_id;
    int data_id;

    // -- Public Class Methods --
    //

    //-------------------------------------------------------------------------
    /*
     * Displays the current value of the transaction or data described by this
     * instance in a human-readable format on the standard output. Each line of
     * the output will be prefixed with the specified prefix. This method prints
     * the value returned by the psdisplay() method.
     */
    virtual function void display(string prefix = "");
    endfunction : display

    //-------------------------------------------------------------------------
    /*
     * Copies the current value of the object instance to the specified object instance.
     * If no   target object instance is specified, a new instance is allocated. Returns
     * a reference to the target instance.
     */
    virtual function Transaction copy(Transaction to = null);
      return null;
    endfunction : copy

    //-------------------------------------------------------------------------
    /*
     * Compares the current value of the object instance with the current value of
     * the specified object instance, according to the specified kind. Returns TRUE
     * (i.e., non-zero) if the value is identical. If the value is different, FALSE is
     * returned and a descriptive text of the first difference found is returned in the
     * specified stringvariable. The kind argument may be used to implement different
     * comparison functions (e.g., full compare, comparison of rand properties only,
     * comparison of all properties physically implemented in a protocol and so on.)
     */
    virtual function bit compare(input Transaction to, output string diff, input int kind = -1);
      return 1'b0;
    endfunction : compare

  endclass : Transaction

  // --------------------------------------------------------------------------
  // -- Transaction mailbox
  // --------------------------------------------------------------------------
  typedef mailbox #(Transaction) tTransMbx;

