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
class FrameLinkUEditTransaction #(int offsetWidth = 8,int enMask = 1) extends Transaction;

   int show_edit     = 0;
   int show_insert   = 0;

   //! Max size in bytes
   int packetSizeMax = 32;
   //! Min size in bytes
   int packetSizeMin = 8;

   //! Randomized transaction data [array of bytes]
   rand byte unsigned data[];

   //! Randomized new data transaction
   rand byte unsigned newData[3:0];
   rand bit[3:0] mask;
   rand bit[offsetWidth-1:0] offset;
   rand bit insertData;
   rand bit editData;

   //! Static parameter for the constraint generator. If value equals to  0,
   //! mask bitmak will be filled with 1 on all positions.
   int maskEnabled = enMask;

   /**
    * Length constraint.
    */
   constraint c1 {
      data.size inside {[packetSizeMin:packetSizeMax]};
   };

   /**
    * Mask constraint.
    */
   constraint c2 {
                (insertData == 1 || maskEnabled == 0) -> (mask == 15);
              };
   /**
    * Offset constraint.
    */
   //constraint c3 {
   //         offset inside {[0:255]};
   //           };

   /**
    * Insret constraint.
    */
  constraint c5 {
            insertData dist{0 := 1, 1 := 1};
   };

   /**
    * Edit constraint.
    */
   constraint c4 {
            editData inside{0,1};
            (insertData == 1) -> (editData == 1);
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

      $write("New data: ");
      for (integer j=0; j < 4; j++)
      begin
         $write("%x ",newData[j]);
      end
      $write("\n");

      $write("Mask: ");
      for(integer j = 0; j < 4;j++)
      begin
        $write("%1b",mask[j]);
      end
      $write("\n");

      tmp = offset;
      $write("Offset: %d\n",tmp);
      $write("Insert: %d\n",insertData);
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

      tr.newData     = newData;
      tr.mask        = mask;
      tr.offset      = offset;
      tr.maskEnabled = maskEnabled;
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

      if((data.size) > offset*4)
      begin
         if(insertData == 1)
           begin
               if(show_insert == 1)
               begin
                  $write("Inserting data\n");
                  this.display();
               end
               // Change the packet size max ...
               tr.packetSizeMax = packetSizeMax + 4;
               // Insert new data on given offset
               tr.data = new[data.size+4];
               tmpOrigIndex = 0;
               for(int j=0;j<tr.data.size;j++)
                   if(j >=offsetStart && j <= offsetEnd)
                     begin
                       //Copy the data from the newData
                       tr.data[j] = newData[j-offsetStart];
                      end
                   else
                     begin
                       //Copy original data and move the index in original data
                       tr.data[j] = data[tmpOrigIndex];
                       tmpOrigIndex++;
                     end
               if(show_insert == 1)
               begin
                  tr.display();
               end
           end //End if
         else
           begin
               // Don't change the packet size max ...
               tr.packetSizeMax = packetSizeMax;
               // Edit data on given offset
               tr.data = new[data.size];
               tr.data = data;
               // Extract  data and edit them
               if(editData == 1)
                  begin
                     if(show_edit == 1)
                     begin
                        $write("Enable editing data\n");
                        this.display();
                     end
                     for(int j=0;j<4;j++)
                     begin
                        if(mask[j] == 1)
                           // Copy change data in actual position
                           tr.data[j+offsetStart] = newData[j];
                     end
                  end
               else
                  begin
                     if(show_edit == 1)
                     begin
                        $write("Disable editing data\n");
                        this.display();
                     end
                  end

               if(show_edit == 1)
               begin
                  tr.display();
               end
            end // End if
         end
      else
         begin

            if(show_edit == 1 || show_insert == 1)
            begin
               $write("BIG DATA - offset: %0d, size: %0d\n", offset*4, data.size-1);
            end
            // Don't change the packet size max ...
            tr.packetSizeMax = packetSizeMax;
            // Edit data on given offset
            tr.data = new[data.size];
            tr.data = data;
            if(show_edit == 1 || show_insert == 1)
            begin
               tr.display();
            end
         end

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
         diff = $sformatf( "packetSize does not match");
      end

      for (integer j=0; j < data.size; j++)
         if (data[j] != tr.data[j])
         begin
            same = 0;
            diff = $sformatf( "data[%0d] does not match", j);
         end

      // Now, compare the data from the FLU Edit transaction
      for (integer j=0; j < 4; j++)
          if(newData[j] != tr.newData[j])
          begin
             same = 0;
             diff = $sformatf( "new data[%0d] does not match", j);
          end

      for (integer j=0; j < 4;j++)
          if(mask[j] != tr.mask[j])
          begin
             same = 0;
             diff = $sformatf( "mask [%0d] does not match", j);
          end

      for (integer j=0; j < offsetWidth;j++)
          if(offset[j] != tr.offset[j])
          begin
             same = 0;
             diff = $sformatf( "offset [%0d] does not match", j);
          end

      if(insertData != tr.insertData)
      begin
         same = 0;
         diff = $sformatf( "insertData command does not match");
      end

      if(maskEnabled != tr.maskEnabled)
      begin
         same = 0;
         diff = $sformatf( "maskEnabled parameter does not match");
      end

      compare = same;
   endfunction: compare

endclass: FrameLinkUEditTransaction
