/*!
 * \file custom_trans.sv
 * \brief Custom transaction
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_common_pkg::*;

class CustomTransaction #(HDR_SIZE = 4, ITEM_WIDTH = 8) extends Transaction;

   rand bit [HDR_SIZE*ITEM_WIDTH-1 : 0] hdr;
   rand int switch = 0;
   rand bit payload = 0;
   rand bit [ITEM_WIDTH-1 : 0] data[];
   int dataSizeMax = 256;
   int dataSizeMin = 32;
   int switchRate = 80;
   int payloadRate = 80;

   constraint c1 {
      payload dist {1 := payloadRate, 0 := (100-payloadRate)};
      data.size inside {[dataSizeMin:dataSizeMax]};
      switch inside {[0:SPLITTER_OUTPUTS-1]};
   };

   virtual function void display(string prefix = "");
      if(prefix != "") begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
      end
      $write("HDR: 0x%h\n", hdr);
      $write("SWITCH: %1d\n", switch);
      $write("PAYLOAD: %1b\n", payload);
      if (payload) begin
         $write("DATA SIZE: %1d ITEMS, DATA:", data.size);
         for (int j=0; j < data.size; j++) begin
            if (j%8==0) $write("\n\t");
            if (j%8==0) $write(" ");
            $write("%x ",data[j]);
         end
         $write("\n");
      end
      $write("\n");
   endfunction

   virtual function Transaction copy(Transaction to = null);
      CustomTransaction #(HDR_SIZE,ITEM_WIDTH) tr;

      if (to == null)
         tr = new();
      else
         $cast(tr, to);

      tr.hdr = hdr;
      tr.switch = switch;
      tr.payload = payload;
      tr.data = data;
      tr.dataSizeMax = dataSizeMax;
      tr.dataSizeMin = dataSizeMin;
      copy = tr;
   endfunction

   virtual function bit compare(input Transaction to, output string diff, input int kind = -1);
      CustomTransaction #(HDR_SIZE,ITEM_WIDTH) tr;
      $cast(tr, to);

      if (hdr != tr.hdr) begin
         $write("Header does not match!\n");
         return 0;
      end
      if (switch != tr.switch) begin
         $write("Switch does not match!\n");
         return 0;
      end
      if (payload != tr.payload) begin
         $write("Payload does not match!\n");
         return 0;
      end
      if (payload) begin
         if (data != tr.data) begin
            if (data.size != tr.data.size) begin
               $write("Data size does not match!\n");
            end else begin
               for (int j=0; j < data.size; j++) begin
                  if (data[j] != tr.data[j]) begin
                     $write("Data items #%1d does not match!\n", j);
                     break;
                  end
               end
            end
            return 0;
         end
      end

      return 1;
   endfunction

endclass
