/*
 * wl_meter.sv: Word Link speed meter
 * Copyright (C) 2016 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */


/**
 * Word Link speed meter.
 */
class WordLinkMeter #(int pDataWidth=512) extends Monitor;


   virtual iWordLinkProbe.monitor #(pDataWidth) dc;
   int working, waiting, nodata;


   function new(string inst, virtual iWordLinkProbe.monitor#(pDataWidth) dc);
      super.new(inst);
      this.enabled     = 0;
      this.busy        = 0;
      this.dc          = dc;
      this.inst        = inst;
   endfunction

   task run();
      working = 0;
      waiting = 0;
      nodata = 0;
      while (enabled) begin
         @(dc.monitor_cb);
         if(dc.monitor_cb.SRC_RDY) begin
           if(dc.monitor_cb.DST_RDY)
             working = working + 1;
           else
             waiting = waiting + 1;
         end else
            nodata = nodata + 1;
      end
   endtask

endclass
