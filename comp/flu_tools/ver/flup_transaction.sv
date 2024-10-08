/**
 * \file flup_transaction.sv
 * \brief FrameLinkUnaligned Plus Transaction
 * \author Jan Kučera <xkucer73@stud.fit.vutbr.cz>
 * \date 2015
 */

/**
 * Copyright (C) 2015 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id:
 *
 */

/**
 * FrameLinkUnaligned Plus Transaction Class
 */
class FrameLinkUPTransaction extends Transaction;

   // -- Public Class Atributes --

   // Data max size in bytes
   int dataSizeMax = 32;
   // Data min size in bytes
   int dataSizeMin = 8;
   // Header size in bytes
   int headerSize = 128;
   // NUM of CHANNELS
   int unsigned channels_num = 16000;

   // Randomized transaction data [array of bytes]
   rand byte unsigned data[];
   // Randomized transaction header [array of bytes]
   rand byte unsigned header[];
   // Randomized transaction channel
   rand int  unsigned channel = 0;

   // Transaction data & header length constraint
   constraint constr {
      data.size inside {[dataSizeMin:dataSizeMax]};
      header.size == headerSize;
      channel     < channels_num;
   };


   // -- Public Class Methods --


   /**
    * Copy constructor.
    */
   virtual function Transaction copy(Transaction to = null);
      FrameLinkUPTransaction tr;
      if (to == null)
         tr = new();
      else
         $cast(tr, to);

      tr.dataSizeMax = dataSizeMax;
      tr.dataSizeMin = dataSizeMin;
      tr.headerSize = headerSize;

      tr.channels_num = channels_num;

      tr.data = new[data.size];
      tr.data = data;

      tr.header = new[header.size];
      tr.header = header;

      tr.channel = channel;

      copy = tr;
   endfunction: copy

   /**
    * Display transaction
    */
   virtual function void display(string prefix = "");
      if (prefix != "")
      begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
      end

      $write("Header size: %1d, Data:", header.size);
      for (integer j = 0; j < header.size; j++)
      begin
         if (j%32==0) $write("\n%4x:", j);
         if (j%8==0) $write(" ");
         $write("%x ", header[j]);
      end
      $write("\n");

      $write("Data size: %1d, Data:", data.size);
      for (integer j = 0; j < data.size; j++)
      begin
         if (j%32==0) $write("\n%4x:", j);
         if (j%8==0) $write(" ");
         $write("%x ", data[j]);
      end
      $write("\n");

      $write("Channel: %1d", channel);

      $write("\n\n");
   endfunction: display

   /**
    * Compare header
    */
   virtual function bit compareHeader(input FrameLinkUPTransaction tr, output string diff, input int kind = -1);
      for (int j = 0; j < header.size; j++)
         if (header[j] != tr.header[j]) begin
            diff = $sformatf( "SZE header: byte %0d does not match", j);
            return 0;
         end
      return 1;
   endfunction: compareHeader

   /**
    * Compare data
    */
   virtual function bit compareData(input FrameLinkUPTransaction tr, output string diff, input int kind = -1);
      for (int j = 0; j < data.size; j++)
         if (data[j] != tr.data[j]) begin
            diff = $sformatf( "Data: byte %0d does not match", j);
            return 0;
         end
      return 1;
   endfunction: compareData

   /**
    * Compare transactions
    */
   virtual function bit compare(input Transaction to, output string diff, input int kind = -1);
      FrameLinkUPTransaction tr;
      $cast(tr, to);

      // Header size
      if (header.size != tr.header.size) begin
         diff = "Header size does not match";
         return 0;
      end

      // Header
      if (!compareHeader(tr, diff, kind))
         return 0;

      // Data size
      if (data.size != tr.data.size) begin
         diff = "Data size does not match";
         return 0;
      end

      // Data
      if (!compareData(tr, diff, kind))
         return 0;

      // Channel
      if (channel != tr.channel) begin
         diff = "Channel does not match";
         return 0;
      end

      return 1;
   endfunction: compare

endclass: FrameLinkUPTransaction

