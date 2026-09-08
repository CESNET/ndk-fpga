// sequence_item.sv: Virtual base sequence
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause


class sequence_mvb #(
   int unsigned ITEMS,
   int unsigned ITEM_WIDTH
) extends  uvm_sequence #(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH+$clog2(ITEMS)));
   `uvm_object_utils(test::sequence_mvb #(ITEMS, ITEM_WIDTH))

   // ------------------------------------------------------------------------
   // Variables

   int unsigned transaction_count_max = 100;
   int unsigned transaction_count_min = 10;
   rand int unsigned transaction_count;
   rand int unsigned rdy_probability;

   constraint tr_cnt_cons {transaction_count inside {[transaction_count_min:transaction_count_max]};}

   constraint c_rdy_probability {
        rdy_probability dist {
           `ndk_rand_dist_first(5, 100, 8) :/ 10,
           `ndk_rand_dist      (5, 100, 8, 1)  :/ 8,
           `ndk_rand_dist      (5, 100, 8, 2)  :/ 3,
           `ndk_rand_dist      (5, 100, 8, 3)  :/ 1,
           `ndk_rand_dist      (5, 100, 8, 4)  :/ 10,
           `ndk_rand_dist      (5, 100, 8, 5)  :/ 30,
           `ndk_rand_dist      (5, 100, 8, 6)  :/ 80,
           `ndk_rand_dist_last (5, 100, 8) :/ 100
        };
    }

   // ------------------------------------------------------------------------
   // Constructor
   function new(string name = "");
      super.new(name);
   endfunction


   // ------------------------------------------------------------------------
   // Generates transactions
   task body();
      if (ITEMS > 1) begin
         bit [$clog2(ITEMS)-1:0] position[ITEMS];

         for(int unsigned it = 0; it < ITEMS; it++) begin
            position[it] = it;
         end

         for (int unsigned it = 0; it < transaction_count; it++) begin
            req = uvm_mvb::sequence_item#(ITEMS, ITEM_WIDTH + $clog2(ITEMS))::type_id::create("req", m_sequencer);

            position.shuffle();

            start_item(req);

            req.randomize() with {
               req.src_rdy dist  {
                  1'b1 :/ rdy_probability,
                  1'b0 :/ rdy_probability < 100 ? 100-rdy_probability : 0
               };
            };

            // Set key field values procedurally after randomization
            foreach (req.data[i]) begin
               if (req.vld[i]) begin
                  req.data[i][ITEM_WIDTH +: $clog2(ITEMS)] = position[i];
               end
            end

            finish_item(req);

            get_response(rsp);
            while (rsp.src_rdy && !rsp.dst_rdy) begin
               start_item(req);
               finish_item(req);

               get_response(rsp);
            end

         end
      end else begin
         // ITEMS == 1: No key field, simple pass-through
         for (int unsigned it = 0; it < transaction_count; it++) begin
            req = uvm_mvb::sequence_item#(ITEMS, ITEM_WIDTH)::type_id::create("req", m_sequencer);

            start_item(req);

            req.randomize() with {
               req.src_rdy dist  {
                     1'b1 :/ rdy_probability,
                     1'b0 :/ rdy_probability < 100 ? 100-rdy_probability : 0
               };
            };

            finish_item(req);

            get_response(rsp);
            while (rsp.src_rdy && !rsp.dst_rdy) begin
               start_item(req);
               finish_item(req);

               get_response(rsp);
            end
         end
      end
   endtask
endclass

