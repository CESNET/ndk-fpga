/*
 * flue_transaction.sv: FrameLinkUnaligned Transaction with edit information
 * Copyright (C) 2015 CESNET
 * Author(s): Pavel Benacek  <benacek@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */

import sv_common_pkg::*;
import sv_flu_pkg::*;

/** FrameLinkUnaligned with Edit Transaction.
 * This class describes transaction and simplifies transaction random
 * generation.
 */
class FrameLinkUEditTransaction #(int offsetWidth = 10) extends Transaction;

   //! Max size in bytes
   int packetSizeMax = 32;
   //! Min size in bytes
   int packetSizeMin = 8;

   //! Randomized transaction data [array of bytes]
   rand byte unsigned data[];

   //! Randomized new data transaction
   rand bit[offsetWidth-1:0] offset;

   /**
    * Length constraint.
    */
   constraint c1 {
      data.size inside {[packetSizeMin:packetSizeMax]};
   };

   /**
    * Offset constraint.
    */
   constraint c3 {
            offset inside {[0:data.size/4-1]};
              };

   // -- Public Class Methods --

   /**
    * Display transaction.
    * Displays the current value of the transaction or data described by this
    * instance in a human-readable format on the standard output. Each line of
    * the output will be prefixed with the specified prefix. This method prints
    * the value returned by the psdisplay() method.
    *
    * @param prefix Any text to be displayed
    *        at the beginning of each output line.
    */
   virtual function void display(string prefix = "");
      // Temporal variable for computation of 4byte shift
      integer tmp;

      if (prefix != "")
      begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
      end

      $write("Packet size: %1d, Data:", data.size);

      for (integer j=0; j < data.size; j++)
      begin
         if (j%32==0) $write("\n%4x:",j);
         if (j%8==0) $write(" ");
         $write("%x ",data[j]);
      end
      $write("\n");

      tmp = offset;
      $write("Offset: %d\n",tmp);
   endfunction : display

   /**
    * Copy constructor.
    */
   virtual function Transaction copy(Transaction to = null);
      FrameLinkUEditTransaction tr;
      if (to == null)
         tr = new();
      else
         $cast(tr, to);

      tr.data          = new[data.size];
      tr.data          = data;
      tr.packetSizeMax = packetSizeMax;
      tr.packetSizeMin = packetSizeMin;

      tr.offset      = offset;
      copy = tr;
   endfunction: copy

   /**
    * Convert the FLU Edit transaction to FLU Transaction
    */
   function Transaction toFLU(Transaction to = null);
      byte unsigned tmpEditData[3:0];
      int offsetStart;
      int offsetEnd;
      int tmpOrigIndex;
      FrameLinkUTransaction tr;
      if (to == null)
         tr = new();
      else
         $cast(tr, to);

      // Here, we need to modify the data with respect
      // to edit information
      //
      // Allocate the place for data. Compute indexes
      offsetStart = 4*offset;
      offsetEnd = 4*offset + 4 - 1;
      //$write("Start offset = %d ; End offset = %d\n",offsetStart,offsetEnd);

            // Don't change the packet size max ...
            tr.packetSizeMax = packetSizeMax;
            // Edit data on given offset
            tr.data = new[4];
            // Extract  data and edit them

            //$write("Get block data\n");
            //this.display();

            for(int j=0;j<4;j++)
            begin
               tr.data[j] = data[j+offsetStart];
            end

            //tr.display();

      // Setup common part of data
      tr.packetSizeMin = packetSizeMin;
      toFLU = tr;
   endfunction : toFLU

   /**
    * Compare transactions.
    * Compares the current value of the object instance with the current value
    * of the specified object instance, according to the specified kind.
    * Returns TRUE (i.e., non-zero) if the value is identical. If the value is
    * different, FALSE is returned and a descriptive text of the first
    * difference found is returned in the specified stringvariable. The kind
    * argument may be used to implement different comparison functions (e.g.,
    * full compare, comparison of rand properties only, comparison of all
    * properties physically implemented in a protocol and so on.)
    *
    * @param to Target transaction for comparison
    * @param diff Output string containing thr first difference
    * @param kind Kind of comparison. Unused yet.
    */
   virtual function bit compare(input Transaction to,
                                output string diff, input int kind = -1);
      bit same = 1; // Suppose that are same
      FrameLinkUEditTransaction tr;
      $cast(tr, to);

      if (data.size != tr.data.size)
      begin
         same = 0;
         diff = "packetSize does not match";
      end

      for (integer j=0; j < data.size; j++)
         if (data[j] != tr.data[j])
         begin
            same = 0;
            diff = $sformatf( "data[%0d] does not match", j);
         end

      for (integer j=0; j < offsetWidth;j++)
          if(offset[j] != tr.offset[j])
          begin
             same = 0;
             diff = $sformatf( "offset [%0d] does not match", j);
          end

      compare = same;
   endfunction: compare

endclass: FrameLinkUEditTransaction
