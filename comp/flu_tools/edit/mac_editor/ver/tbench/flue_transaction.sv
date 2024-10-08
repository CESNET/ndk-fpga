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
class FrameLinkUEditTransaction #() extends Transaction;

   //! Max size in bytes
   int packetSizeMax = 32;
   //! Min size in bytes
   int packetSizeMin = 8;

   //! Randomized transaction data [array of bytes]
   rand byte unsigned data[];

   //! Randomized new data transaction
   rand byte unsigned dstData[5:0];
   rand byte unsigned srcData[5:0];
   rand bit[5:0] dstMask;
   rand bit[5:0] srcMask;
   rand bit dstW;
   rand bit srcW;

   /**
    * Length constraint.
    */
   constraint c1 {
      data.size inside {[packetSizeMin:packetSizeMax]};
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

      $write("dst Write: %1b\n", dstW);
      $write("dst Data: ");
      for (integer j=0; j < 6; j++)
      begin
         $write("%x ",dstData[j]);
      end
      $write("\n");
      $write("dst Mask: ");
      for(integer j = 0; j < 6;j++)
      begin
        $write("%1b",dstMask[j]);
      end
      $write("\n");

      $write("src Write: %1b\n", srcW);
      $write("src Data: ");
      for (integer j=0; j < 6; j++)
      begin
         $write("%x ",srcData[j]);
      end
      $write("\n");
      $write("src Mask: ");
      for(integer j = 0; j < 6;j++)
      begin
        $write("%1b",srcMask[j]);
      end
      $write("\n");
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
      tr.dstData       = dstData;
      tr.dstMask       = dstMask;
      tr.dstW          = dstW;
      tr.srcData       = srcData;
      tr.srcMask       = srcMask;
      tr.srcW          = srcW;
      copy = tr;
   endfunction: copy

   /**
    * Convert the FLU Edit transaction to FLU Transaction
    */
   function Transaction toFLU(Transaction to = null);
      int tmpOrigIndex;
      int show;
      FrameLinkUTransaction tr;
      if (to == null)
         tr = new();
      else
         $cast(tr, to);

      show = 0;
      tr.packetSizeMax = packetSizeMax;
      tr.data = new[data.size];


      tmpOrigIndex = 0;
      for(int j=0;j<tr.data.size;j++)
      begin
        //Copy original data and move the index in original data
        tr.data[j] = data[tmpOrigIndex];
        tmpOrigIndex++;
      end

      if(show == 1)
      begin
         $write("####\n");
         this.display();
      end

      if(dstW == 1)
      begin
         for(int j=0;j<6;j++)
         begin
            if(dstMask[j] == 1)
            begin
               tr.data[j] = dstData[j];
            end
         end
      end

      if(srcW == 1)
      begin
         for(int j=0;j<6;j++)
         begin
           if(srcMask[j] == 1)
           begin
             tr.data[j+6] = srcData[j];
           end
         end
      end

      if(show == 1)
      begin
         tr.display();
         $write("----\n");
      end

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
         diff = $sformatf( "packetSize does not match");
      end

      for (integer j=0; j < data.size; j++)
         if (data[j] != tr.data[j])
         begin
            same = 0;
            diff = $sformatf( "data[%0d] does not match", j);
         end

      for (integer j=0; j < 6; j++)
          if(dstData[j] != tr.dstData[j])
          begin
             same = 0;
             diff = $sformatf( "dst  data[%0d] does not match", j);
          end

      for (integer j=0; j < 6; j++)
          if(srcData[j] != tr.srcData[j])
          begin
             same = 0;
             diff = $sformatf( "src data[%0d] does not match", j);
          end

      for (integer j=0; j < 6;j++)
          if(dstMask[j] != tr.dstMask[j])
          begin
             same = 0;
             diff = $sformatf( "dst mask [%0d] does not match", j);
          end

      for (integer j=0; j < 6;j++)
          if(srcMask[j] != tr.srcMask[j])
          begin
             same = 0;
             diff = $sformatf( "src mask [%0d] does not match", j);
          end

      if(dstW != tr.dstW)
      begin
         same = 0;
         diff = $sformatf( "dst write command does not match");
      end

      if(srcW != tr.srcW)
      begin
         same = 0;
         diff = $sformatf( "src write command does not match");
      end

      compare = same;
   endfunction: compare

endclass: FrameLinkUEditTransaction
