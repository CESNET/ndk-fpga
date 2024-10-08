/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

class avalon_rc_driver extends sv_common_pkg::Driver;

    avst_tx::transaction tr_low;
    int unsigned verbosity = 0;
    ifg_delay delay;

    ////////////////////
    // functions
    function new(string inst, sv_common_pkg::tTransMbx mbx);
        super.new(inst, mbx);
        delay = new();
    endfunction

    function void ifg_set(ifg_delay cfg);
        delay = cfg;
    endfunction

    task run();
        while(enabled == 1'b1) begin
            send_packet();

            assert(delay.randomize());
            if(delay.enabled == 1'b1) begin
                for (int unsigned it = 0; it < delay.length; it++) begin
                    send_empty_frame();
                end
            end
        end
    endtask

    function void verbosity_set(int unsigned level);
        verbosity = level;
    endfunction

    //send emty frame
    task send_empty_frame();
         sv_common_pkg::Transaction tr_send;
         tr_low = new();
         assert(tr_low.randomize() with {valid == 0;});

         if (verbosity > 2) begin
            tr_low.display({inst, " SEND EMPTY FRAME"});
         end

         $cast(tr_send, tr_low);
         foreach (cbs[i])
             cbs[i].pre_tx(tr_send, inst);
         /* No-op = virtual driver */
         foreach (cbs[i])
             cbs[i].post_tx(tr_send, inst);
    endtask

    //send fram in one block
    task send_packet();
        logic [128-1:0] hdr;
        logic [9:0] tag;
        PcieCompletion tr;
        sv_common_pkg::Transaction tr_send;
        sv_common_pkg::Transaction tr_recv;
        int unsigned cycle_max;

        transMbx.get(tr_recv);
        $cast(tr, tr_recv);

         if (verbosity) begin
             tr_recv.display({inst, " GET FRAME"});
         end


        for(int unsigned it = 0; it < tr.data.size(); it += 8) begin
          tr_low = new();
          assert(tr_low.randomize());

          //init
          tr_low.sop = 1'b0;
          tr_low.eop = 1'b0;
          tr_low.valid = 1'b1;
          tr_low.empty = 0;
          tr_low.bar_range = '0;

          //set sop
          if (it == 0) begin
            tr_low.sop        = 1'b1;

            tag = tr.tag;
            tr_low.bar_range  = '0;
            tr_low.prefix     = '0;
            tr_low.vf_active = 1'b1;
            tr_low.vf_num = tr.requester_id[8-1:0];

            hdr[95:80] = tr.requester_id; //request id
            hdr[79:72] = tr.tag[7:0]; //tag
            hdr[71]    = 1'b0;
            hdr[70:64] = tr.lower_address[6:0]; //lower ADDR
            hdr[63:48] = '0; //completer ID
            hdr[47:45] = 3'b000; // Compl. Status
            hdr[44]    = 1'b0;
            hdr[43:32] = tr.byte_count; //Byte count;
            hdr[31:24] = 8'b01001010;
            hdr[23]    = tag[9]; //T9
            hdr[22:20] = 3'b000; //TC - Trafic class
            hdr[19]    = tag[8]; //T8
            hdr[18:16] = '0;
            hdr[15]    = 1'b0; //TD
            hdr[14]    = 1'b0; //EP
            hdr[13:12] = 2'b00; //ATTR => ordering
            hdr[11:10] = '0;
            hdr[9:0]   = tr.length; //DWORD COUNT

            tr_low.hdr[128-1:96] = hdr[32-1:0];
            tr_low.hdr[96-1:64]  = hdr[64-1:32];
            tr_low.hdr[64-1:32]  = hdr[96-1:64];
            tr_low.hdr[32-1:0]   = hdr[128-1:96];
          end

          //set eop
          if (it + 8 < tr.data.size()) begin
              cycle_max = 8;
          end else begin
              cycle_max = tr.data.size() - it;
              tr_low.eop   = 1'b1;
              tr_low.empty = (8 - cycle_max);
          end

          //setup data
          for (int unsigned jt = 0; jt < cycle_max; jt++) begin
              tr_low.data[(jt+1)*32-1 -: 32] = tr.data[it + jt];
          end

          $cast(tr_send, tr_low);
          foreach (cbs[i])
              cbs[i].pre_tx(tr_send, inst);
          /* No-op = virtual driver */
          foreach (cbs[i])
              cbs[i].post_tx(tr_send, inst);

         if (verbosity) begin
             tr_low.display({inst, " SEND FRAME"});
         end

       end
    endtask
endclass

