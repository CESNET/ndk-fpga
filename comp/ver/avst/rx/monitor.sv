/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

class monitor #(AVST_REGIONS) extends sv_common_pkg::Monitor;

    ////////////////////////
    // Variable
    typedef enum {IDLE, READ} state_t;
    state_t state;
    virtual avst_rx_if #(AVST_REGIONS).monitor vif;
    int unsigned verbosity = 0;

    ////////////////////////
    // functions
     function new (string inst, virtual avst_rx_if#(AVST_REGIONS).monitor param_vif);
        super.new(inst);
        this.vif = param_vif;
     endfunction

    function void verbosity_set(int unsigned level);
        verbosity = level;
    endfunction

    task read(int block);
      transaction tr;
      sv_common_pkg::Transaction to;

      if (vif.monitor_cb.RESET == 1'b1) begin
	      return;
	  end

      //if there isnt valid data
      if (vif.monitor_cb.valid[block] == 1'b0) begin
		return;
      end


      tr = new;
      $cast(to, tr);
      foreach(cbs[i]) cbs[i].pre_rx(to, inst);
      tr.sop = vif.monitor_cb.sop[block];
      tr.eop = vif.monitor_cb.eop[block];
      tr.prefix = vif.monitor_cb.prefix[block*32 +:32];
      tr.hdr = vif.monitor_cb.hdr[block*128      +:128];
      tr.data = vif.monitor_cb.data[block*256    +:256];
      foreach(cbs[i]) cbs[i].post_rx(to, inst);
   endtask

   task run();
     state = IDLE;

     //do monitor
     forever begin
       @(vif.monitor_cb)

       for (int it = 0; it < AVST_REGIONS; it++) begin
           read(it);
       end
     end
   endtask
endclass

