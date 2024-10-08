/*
 * wl_transaction.sv: Word Link Transaction
 * Copyright (C) 2015 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

/** Word Link Transaction.
 * This class describes transaction and simplifies transaction random
 * generation.
 */
class WordLinkTransaction extends Transaction;

   //! Size in bytes
   int dataSize = 64;

   //! Randomized transaction data [array of bytes]
   rand byte unsigned data[];

   /**
    * Length constraint.
    */
   constraint c1 {
      data.size inside {[dataSize:dataSize]};
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
      if (prefix != "")
      begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
      end

      $write("Data size: %1d, Data:", data.size);

      for (integer j=0; j < data.size; j++)
      begin
         if (j%32==0) $write("\n%4x:",j);
         if (j%8==0) $write(" ");
         $write("%x ",data[j]);
      end
      $write("\n");
   endfunction : display

   /**
    * Copy constructor.
    */
   virtual function Transaction copy(Transaction to = null);
      WordLinkTransaction tr;
      if (to == null)
         tr = new();
      else
         $cast(tr, to);

      tr.data          = new[data.size];
      tr.data          = data;
      tr.dataSize      = dataSize;
      copy = tr;
   endfunction: copy


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
      WordLinkTransaction tr;
      $cast(tr, to);

      if (data.size != tr.data.size)
      begin
         same = 0;
         diff = $sformatf( "dataSize does not match");
      end

      for (integer j=0; j < data.size; j++)
         if (data[j] != tr.data[j])
         begin
            same = 0;
            diff = $sformatf( "data[%0d] does not match", j);
         end

      compare = same;
   endfunction: compare

endclass: WordLinkTransaction

