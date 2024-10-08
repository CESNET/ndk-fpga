/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

///////////////////////////////////////////////////////////////////////////////
// AVST tx interface
interface avst_tx_if #(REGIONS) (input logic CLK, RESET);

  timeunit      1ns;
  timeprecision 1ps;

  logic [REGIONS*256-1:0] data;
  logic [REGIONS*128-1:0] hdr;
  logic [REGIONS*32-1:0]  prefix;
  logic [REGIONS*1-1:0]   sop;
  logic [REGIONS*1-1:0]   eop;
  logic [REGIONS*3-1:0]   empty;
  logic [REGIONS*1-1:0]   vf_active;
  logic [REGIONS*10-1:0]  vf_num;
  logic [REGIONS*3-1:0]   bar_range;
  logic [REGIONS*1-1:0]   valid;
  logic ready;

  clocking driver_cb @(posedge CLK);
      output data, hdr, prefix, sop, eop, empty, bar_range, valid, vf_active, vf_num;
      input  ready, RESET;
  endclocking;

  clocking monitor_cb @(posedge CLK);
      input data, hdr, prefix, sop, eop, empty, bar_range, valid, vf_active, vf_num;
      input ready, RESET;
  endclocking;

  modport dut(input data, hdr, prefix, sop, eop, empty, bar_range, valid, vf_active, vf_num, output ready);

  modport driver(clocking driver_cb);
  modport monitor(clocking monitor_cb);



  property ready_prop;
      @(posedge CLK) disable iff (RESET)
      (!$isunknown(ready));
  endproperty

  //ON START CLK=0 RESET = 1
  assert property (ready_prop) else begin $error("AVALON TX: ready cannot be undefined if RESET is not set"); $stop(); end
endinterface

