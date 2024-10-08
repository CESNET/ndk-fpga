/*
 * fl_transaction_pkg.sv: FrameLink Transaction
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- FrameLink Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  class FrameLinkTransaction extends Transaction;

     // -- Public Class Atributes --
     // Randomization parameters
     int packetCount     = 3;
     int packetSizeMax[] = '{32,32,32};
     int packetSizeMin[] = '{8,8,8};

     // Randomized transaction data [packet][byte]
     rand byte unsigned data[][];

     // -- Constrains --
     constraint c1 {
       data.size       == packetCount;
       foreach (data[i]) data[i].size inside
         {[packetSizeMin[i]:packetSizeMax[i]]};
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

       for (integer i=0; i < packetCount; i++) begin
         $write("Part no: %1d, Part size: %1d, Data:", i, data[i].size);

         for (integer j=0; j < data[i].size; j++)
         begin
           if (j%16==0) $write("\n%4x:",j);
           if (j%8==0) $write(" ");
           $write("%x ",data[i][j]);
         end
         $write("\n");
       end
       $write("\n");
    endfunction : display



     //-- Copy -----------------------------------------------------------------
     // Copy constructor
     virtual function Transaction copy(Transaction to = null);
       FrameLinkTransaction tr;
       if (to == null)
         tr = new();
       else
         $cast(tr, to);

       tr.packetCount   = packetCount;
       tr.packetSizeMax = new[packetCount];
       tr.packetSizeMin = new[packetCount];
       tr.data          = new [packetCount];
       for (integer i=0; i < packetCount; i++)
         tr.data[i]     = new[data[i].size];

       tr.packetSizeMax = packetSizeMax;
       tr.packetSizeMin = packetSizeMin;
       tr.data          = data;

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
       FrameLinkTransaction tr;
       $cast(tr, to);

       if (packetCount != tr.packetCount)
       begin
         same = 0;
         diff = "packetCount does not match";
       end

       for (integer i=0; i<packetCount; i++)
       begin
         if (data[i].size != tr.data[i].size)
         begin
           same = 0;
           diff = $sformatf( "packetSize[%0d] does not match", i);
         end
       end

       for (integer i=0; i < packetCount; i++)
         for (integer j=0; j < data[i].size; j++)
           if (data[i][j] != tr.data[i][j])
           begin
             same = 0;
             diff = $sformatf( "data[%0d][%0d] does not match", i, j);
           end

       compare = same;
     endfunction: compare

   endclass: FrameLinkTransaction

