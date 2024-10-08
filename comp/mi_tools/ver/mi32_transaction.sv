/*
 * mi32_transaction.sv: Mi32 Transaction
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
 *            Petr Kastovsky <kastovsky@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- Mi32 Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  class Mi32Transaction extends Transaction;

     // -- Public Class Atributes --
     // Randomization parameters
     logic [31:0] maxAddress = '1;
     logic [31:0] minAddress = '0;

     // Randomized transaction parameters
     rand logic [31:0]  address;
     rand logic [31:0]  data;
     rand logic [3:0]   be;
     rand logic         rw; // rw==0 => read request, rw==1 => write request

     // -- Constrains --
     constraint c1 {
       address       <= maxAddress;
       address       >= minAddress;
       };


    // -- Public Class Methods --

    /*
     * Displays the current value of the transaction or data described by this
     * instance in a human-readable format on the standard output. Each line of
     * the output will be prefixed with the specified prefix. This method prints
     * the value returned by the psdisplay() method.
     */
    virtual function void display(string prefix = "");
       if (prefix != "")
       begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
       end

       if (rw == 0) // read request
         $write("Read from address: %08x data: %08x BE: %0x\n", address, data, be);
       else // write request
         $write("Write to address: %08x data: %08x BE: %0x\n", address, data, be);

    endfunction : display



     //-- Copy -----------------------------------------------------------------
     // Copy constructor
     virtual function Transaction copy(Transaction to = null);
       Mi32Transaction tr;
       if (to == null)
         tr = new();
       else
         $cast(tr, to);

       tr.maxAddress    = maxAddress;
       tr.address       = address;
       tr.data          = data;
       tr.be            = be;
       tr.rw            = rw;

       copy = tr;
       endfunction: copy


     // -- Compare --------------------------------------------------------------
     /* Compares the current value of the object instance with the current value
      * of the specified object instance, according to the specified kind.
      * Returns TRUE (i.e., non-zero) if the value is identical. If the value is
      * different, FALSE is returned and a descriptive text of the first
      * difference found is returned in the specified stringvariable. The kind
      * argument may be used to implement different comparison functions (e.g.,
      * full compare, comparison of rand properties only, comparison of all
      * properties physically implemented in a protocol and so on.)
      */
     virtual function bit compare(input Transaction to,
                                  output string diff, input int kind = -1);
       bit same = 1; // Suppose that are same
       logic [31:0] wideBe;
       Mi32Transaction tr;

       if (! $cast(tr, to))
          $display("Cast error\n");

       if (address != tr.address)
       begin
         same = 0;
         diff = "addresses does not match";
       end

       if (be != tr.be)
       begin
         same = 0;
         diff = "byte enable does not match";
       end

       for (int i = 0; i < 32; i++)
          wideBe[i] = tr.be[i / 8];
       if ((data & wideBe) != (tr.data & wideBe))
       begin
         same = 0;
         diff = "data does not match";
       end

       if (rw != tr.rw)
       begin
         same = 0;
         diff = "type/direction does not match";
       end

       compare = same;
     endfunction: compare

   endclass: Mi32Transaction

