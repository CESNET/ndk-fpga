/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

interface avst_rx_if #(REGIONS) (input logic CLK, RESET);

  timeunit      1ns;
  timeprecision 1ps;

  logic [REGIONS*256-1:0] data;
  logic [REGIONS*128-1:0] hdr;
  logic [REGIONS*32-1:0]  prefix;
  logic [REGIONS*1-1:0]   sop;
  logic [REGIONS*1-1:0]   eop;
  logic [REGIONS*1-1:0]   error;
  logic [REGIONS*1-1:0]   valid;
  logic ready = 1'b1;

  clocking driver_cb @(posedge CLK);
      output ready;
      input  data, hdr, prefix, sop, eop, error, valid, RESET;
  endclocking;

  clocking monitor_cb @(posedge CLK);
      input data, hdr, prefix, sop, eop, error, valid;
      input ready, RESET;
  endclocking;

  modport dut(output data, hdr, prefix, sop, eop, error, valid, input ready);

  modport driver(clocking driver_cb);
  modport monitor(clocking monitor_cb);

  property valid_prop;
      @(posedge CLK) disable iff (RESET)
      !$isunknown(valid);
  endproperty

  property valid_set (int index);
      @(posedge CLK) disable iff (RESET)
      (valid[index] === 1'b1) |-> (!$isunknown(sop[index]) && !$isunknown(eop[index]));
  endproperty

  property valid_sop (int index);
      @(posedge CLK) disable iff (RESET)
      (valid[index] === 1'b1 && sop[index]) |->  (!$isunknown(hdr[(index+1)*128-1 -:128]) && !$isunknown(prefix[(index+1)*32-1 -:32]));
  endproperty

  property valid_eop (int index);
      @(posedge CLK) disable iff (RESET)
      (valid[index] === 1'b1 && eop[index]) |->  (!$isunknown(error[index]));
  endproperty



  //ON START CLK=0 RESET=1
  assert property (valid_prop) else begin $error("AVALON RX: valid cannot be undefined if RESET is not set"); $stop(); end

  //assert property (valid_set)  else begin $error("AVALON RX: if VALID is set then all values have to have valid value"); $stop(); end
  generate for (genvar i = 0; i < REGIONS; i++) begin
    assert property (valid_set(i))  else begin $error("AVALON RX: if VALID is set then sop and eop have to be valid"); $stop(); end
    assert property (valid_sop(i))  else begin $error("AVALON RX: if VALID and SOP is set then HEADER and PREFIX have to be valid"); $stop(); end
    assert property (valid_eop(i))  else begin $error("AVALON RX: if VALID and EOP is set then ERROR have to be valid"); $stop(); end
  end
  endgenerate
endinterface

