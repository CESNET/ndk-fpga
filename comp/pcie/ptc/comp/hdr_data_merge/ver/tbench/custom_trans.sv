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

class CustomTransaction #(HDR_WIDTH = 128, PAYLOAD_ITEM_WIDTH = 32) extends Transaction;

   rand bit [HDR_WIDTH-1 : 0] header; // = {HDR_WIDTH{1'b1}};
   rand bit payload_en = 0;
   int payloadSizeMax = 256;
   int payloadSizeMin = 32;
   int payloadRate = 80;
   rand bit [PAYLOAD_ITEM_WIDTH-1 : 0] payload[];

   constraint c1 {
      payload_en dist {1 := payloadRate, 0 := (100-payloadRate)};
      payload.size inside {[payloadSizeMin:payloadSizeMax]};
   };

   virtual function void display(string prefix = "");
      if(prefix != "") begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
      end
      $write("HEADER: 0x%h\n", header);
      $write("PAYLOAD: 0x%1h\n", payload_en);
      if (payload_en == 1) begin
         $write("PAYLOAD SIZE: %1d ITEMS, PAYLOAD DATA:", payload.size);
         for (int j=0; j < payload.size; j++) begin
            if (j%8==0) $write("\n\t");
            //if (j%8==0) $write(" ");
            $write("%x ",payload[j]);
         end
         $write("\n");
      end
   endfunction

   virtual function Transaction copy(Transaction to = null);
      CustomTransaction #(HDR_WIDTH,PAYLOAD_ITEM_WIDTH) tr;

      if (to == null)
         tr = new();
      else
         $cast(tr, to);

      tr.header = header;
      tr.payload_en = payload_en;
      tr.payload = payload;
      tr.payloadSizeMax = payloadSizeMax;
      tr.payloadSizeMin = payloadSizeMin;
      tr.payloadRate = payloadRate;
      copy = tr;
   endfunction

   virtual function bit compare(input Transaction to, output string diff, input int kind = -1);
      CustomTransaction #(HDR_WIDTH,PAYLOAD_ITEM_WIDTH) tr;
      $cast(tr, to);

      if (header != tr.header) begin
         diff = $sformatf( "header does not match");
         return 0;
      end

      if (payload_en != tr.payload_en) begin
         diff = $sformatf( "payload enable does not match");
         return 0;
      end

      if (tr.payload_en == 1) begin
         if (payload != tr.payload) begin
            if (payload.size != tr.payload.size) begin
               diff = $sformatf( "payload size does not match");
            end else begin
               for (int j=0; j < payload.size; j++) begin
                  if (payload[j] != tr.payload[j]) begin
                     diff = $sformatf( "Items #%1d does not match", j);
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
