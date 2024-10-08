/*
 * Copyright (C) 2021 CESNET z. s. p. o.
 * Author(s):
 * SPDX-License-Identifier: BSD-3-Clause
 */

// TODO: coverage for the component

//module asfifo_cov ();
//
//    `define ASFIFO_WR_PATH $root.testbench.DUT_U.VHDL_DUT_U.fifo_in_i
//
//
//    //same clock => I dont know why sigsegv.
//    //WRITE
//    covergroup cov_wr @(posedge $root.testbench.DUT_U.CLK);
//    //covergroup cov @(posedge `ASFIFO_WR_PATH.WR_CLK);
//        full : coverpoint `ASFIFO_WR_PATH.WR_FULL  iff (`ASFIFO_WR_PATH.WR_RST == 1'b0) {
//            bins zero = {0};
//            bins one  = {1};
//        }
//
//        en : coverpoint `ASFIFO_WR_PATH.WR_EN   iff (`ASFIFO_WR_PATH.WR_RST == 1'b0) {
//            bins zero = {0};
//            bins one  = {1};
//        }
//
//        status : coverpoint `ASFIFO_WR_PATH.WR_STATUS  iff (`ASFIFO_WR_PATH.WR_RST == 1'b0) {
//            bins empty   = {0};
//            bins aempty  = {[1:`ASFIFO_WR_PATH.ITEMS/2-1]};
//            bins afull   = {[`ASFIFO_WR_PATH.ITEMS/2:`ASFIFO_WR_PATH.ITEMS]};
//            bins full    = {`ASFIFO_WR_PATH.ITEMS};
//        }
//
//        en_status : cross status, `ASFIFO_WR_PATH.WR_EN;
//    endgroup
//
//    //READ
//    covergroup cov_rd @(posedge $root.testbench.DUT_U.CLK);
//        en : coverpoint `ASFIFO_WR_PATH.RD_EN  iff (`ASFIFO_WR_PATH.RD_RST == 1'b0) {
//            bins zero = {0};
//            bins one  = {1};
//        }
//
//        empty : coverpoint `ASFIFO_WR_PATH.RD_EMPTY iff (`ASFIFO_WR_PATH.RD_RST == 1'b0) {
//            bins zero = {0};
//            bins one  = {1};
//        }
//
//        status : coverpoint `ASFIFO_WR_PATH.RD_STATUS  iff (`ASFIFO_WR_PATH.RD_RST == 1'b0) {
//            bins empty   = {0};
//            bins aempty  = {[1:`ASFIFO_WR_PATH.ITEMS/2-1]};
//            bins afull   = {[`ASFIFO_WR_PATH.ITEMS/2:`ASFIFO_WR_PATH.ITEMS]};
//            bins full    = {`ASFIFO_WR_PATH.ITEMS};
//        }
//
//        en_status : cross en, status;
//    endgroup
//
//    initial begin
//       cov_wr wr;
//       cov_rd rd;
//
//       wr = new();
//       rd = new();
//    end
//endmodule
