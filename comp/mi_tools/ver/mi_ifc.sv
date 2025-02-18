/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

// ----------------------------------------------------------------------------
//                          MI Interface declaration
// ----------------------------------------------------------------------------
interface iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH = 0) (input wire logic CLK, RESET);
  wire logic [ADDR_WIDTH-1:0]    ADDR;  // ADDRess
  wire logic [DATA_WIDTH-1:0]    DWR;   // Data to be WRitten
  wire logic [META_WIDTH-1:0]    MWR;   // META to be WRitten
  wire logic [DATA_WIDTH/8-1:0]  BE;    // Byte Enable
  wire logic RD;           // ReaD request
  wire logic WR;           // WRite request

  logic ARDY;              // Address ReaDY
  logic DRDY;              // Data ReaDY
  logic [DATA_WIDTH-1:0]    DRD;   // Data to be ReaD

  //-- MI32 Clocking Blocks ---------------------------------------------------

  clocking monitor_cb @(posedge CLK);
    input ADDR, DWR, MWR, DRD, BE, RD, WR, ARDY, DRDY;
  endclocking: monitor_cb;

  clocking cb_master @(posedge CLK);
    output  ADDR, DWR, MWR, BE, RD, WR; input RESET, ARDY, DRDY, DRD;
  endclocking;

  //-- MI32 Modports ----------------------------------------------------------
  modport slave  (input   ADDR, DWR, MWR, BE, RD, WR, output ARDY, DRDY, DRD);
  modport master (output  ADDR, DWR, MWR, BE, RD, WR, input ARDY, DRDY, DRD);

  modport tb_slave  (input   ADDR, DWR, MWR, BE, RD, WR, CLK, RESET, output ARDY, DRDY, DRD);
  modport tb_master (clocking cb_master);

  //verification modports
  modport monitor   (clocking monitor_cb);
endinterface


module MI_PROPERTY #(
    parameter int unsigned DIRECTION = 0 //  0 => ASSERT(TX), 1 => ASSUME(RX)
)
(
    iMi inf
);

    property valid;
        @(posedge inf.CLK) disable iff(inf.RESET)
        !$isunknown(inf.RD) && !$isunknown(inf.WR);
    endproperty

    property valid_request;
       @(posedge inf.CLK) disable iff(inf.RESET)
       (inf.RD || inf.WR) |-> (!$isunknown(inf.ADDR) && !$isunknown(inf.BE));
    endproperty

    property valid_request_write_data;
       @(posedge inf.CLK) disable iff(inf.RESET)
       (inf.WR) |-> (!$isunknown(inf.DWR));
    endproperty

    property valid_request_write_meta;
       @(posedge inf.CLK) disable iff(inf.RESET)
       ((inf.RD || inf.WR) && inf.META_WIDTH > 0) |-> (!$isunknown(inf.MWR));
    endproperty

    property valid_response;
       @(posedge inf.CLK) disable iff(inf.RESET)
       (inf.DRDY) |-> (!$isunknown(inf.DRD));
    endproperty

    // --------------------------------------------------------------------------
    // -- Interface properties/assertions
    // --------------------------------------------------------------------------
    // -- While RESET RD inactive ----------------------------------------
    // RD or WR may be active only if RESET is inactive.
    property prop_inactive_when_reset;
       @(posedge inf.CLK) (inf.RESET)|->(not (inf.RD || inf.WR));
    endproperty

    // -- WR never together with RD ---------------------------------------
    // WR can not be active together with RD.
    property no_RDWR ;
       @(posedge inf.CLK) disable iff (inf.RESET)
       !(inf.RD & inf.WR);
    endproperty


    generate
        if (DIRECTION == 0) begin
            assert property (prop_inactive_when_reset) else begin $error("RD or WR is active during reset."); $stop(); end;
            assert property (valid)                    else begin $error("signlas RD and WR have to be allways valid"); $stop(); end
            assert property (valid_request)            else begin $error("signal addr and be have to be valid when RD or WR signal is asserted"); $stop(); end
            assert property (valid_request_write_data) else begin $error("when signal WR is asserted then signal DWR have to be valid"); $stop(); end
            assert property (valid_request_write_meta) else begin $error("when signal WR is asserted and META_WIDTH > 0 then signal MWR have to be valid"); $stop(); end
            assert property (valid_response)           else begin $error("when signal DRDY is asserted then signal DRD have to be valid"); $stop(); end
            assert property (no_RDWR)                  else begin $error("RD and WR signals can not be active at the same cycle."); $stop(); end
        end else if (DIRECTION == 1) begin
            assume property (prop_inactive_when_reset) else begin $warning("RD or WR is active during reset."); end;
            assume property (valid)                    else begin $warning("signlas RD and WR have to be allways valid");end
            assume property (valid_request)            else begin $warning("signal addr and be have to be valid when RD or WR signal is asserted"); end
            assume property (valid_request_write_data) else begin $warning("when signal WR is asserted then signal DWR have to be valid"); end
            assume property (valid_request_write_meta) else begin $warning("when signal WR is asserted and META_WIDTH > 0 then signal MWR have to be valid"); end
            assume property (valid_response)           else begin $warning("when signal DRDY is asserted then signal DRD have to be valid"); end
            assume property (no_RDWR)                  else begin $warning("RD and WR signals can not be active at the same cycle."); end
        end else begin
            initial assert (0) else begin $error("%s\nUNSUPORTED DIRECTION %0d", `__FILE__, DIRECTION); $stop(); end
        end
    endgenerate
endmodule


