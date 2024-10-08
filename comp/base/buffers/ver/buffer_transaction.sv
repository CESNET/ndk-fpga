/*
 * buffer_transaction.sv: Transaction
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta03@stud.fit.vutbr.cz>
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
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  class BufferTransaction extends Transaction;

    // -- Public Class Atributes --
    // Randomization parameters
    int dataSize     = 64;
    int flowCount    = 8;


    // Randomized data
    rand bit unsigned data[];
    rand int unsigned num_block_addr;

    // -- Constrains --
     constraint c1 {
       data.size       == dataSize;
       num_block_addr inside {[0:(flowCount-1)]};
       };


    // -- Public Class Methods --

    /*
     * Displays the current value of the transaction or data described by this
     * instance in a human-readable format on the standard output. Each line of
     * the output will be prefixed with the specified prefix. This method prints
     * the value returned by the psdisplay() method.
     */
    virtual function void display(string prefix = "");
       byte unsigned dataToWrite[] = new [dataSize/8];
       int m=0;

       if (prefix != "")
       begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
       end
//       $write("dataToWrite.size:%d\n",dataToWrite.size);
       $write("Block_addr: %d Data: ", num_block_addr);

       for (int i=0; i<dataToWrite.size; i++)
         for (int j=0; j<8; j++)
           dataToWrite[i][j]=data[m++];

       for (integer j=0; j < dataToWrite.size; j++)
         $write("%x",dataToWrite[j]);
       $write("\n");

    endfunction : display



     //-- Copy -----------------------------------------------------------------
     // Copy constructor
     virtual function Transaction copy(Transaction to = null);
       BufferTransaction tr;
       if (tr == null)
         tr = new();
       else
         $cast(tr, to);

       tr.dataSize       = dataSize;
       tr.flowCount      = flowCount;
       tr.num_block_addr = num_block_addr;
       tr.data           = new [dataSize];

       tr.data = data;

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
       BufferTransaction tr;
       $cast(tr, to);


       if (dataSize != tr.dataSize)
         begin
           same = 0;
           diff = "dataSize does not match";
         end

       if (num_block_addr != tr.num_block_addr)
         begin
           same = 0;
           diff = "BlockAddr does not match";
         end

       for (integer i=0; i < data.size; i++)
         if (data[i] != tr.data[i])
           begin
             same = 0;
             diff = "data[] does not match";
           end

       compare = same;
     endfunction: compare

   endclass: BufferTransaction

