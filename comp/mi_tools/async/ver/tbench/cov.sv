/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

module asfifo_cov ();

    `define ASFIFO_WR_PATH $root.testbench.DUT_U.VHDL_DUT_U.fifo_in_i


    //same clock => I dont know why sigsegv.
    //WRITE
    covergroup cov_wr @(posedge $root.testbench.DUT_U.MASTER_CLK);
    //covergroup cov @(posedge `ASFIFO_WR_PATH.WR_CLK);
        full : coverpoint `ASFIFO_WR_PATH.WR_FULL  iff (`ASFIFO_WR_PATH.WR_RST == 1'b0) {
            bins zero = {0};
            bins one  = {1};
        }

        en : coverpoint `ASFIFO_WR_PATH.WR_EN   iff (`ASFIFO_WR_PATH.WR_RST == 1'b0) {
            bins zero = {0};
            bins one  = {1};
        }

        status : coverpoint `ASFIFO_WR_PATH.WR_STATUS  iff (`ASFIFO_WR_PATH.WR_RST == 1'b0) {
            bins empty   = {0};
            bins aempty  = {[1:`ASFIFO_WR_PATH.ITEMS/2-1]};
            bins afull   = {[`ASFIFO_WR_PATH.ITEMS/2:`ASFIFO_WR_PATH.ITEMS]};
            bins full    = {`ASFIFO_WR_PATH.ITEMS};
        }

        en_status : cross status, `ASFIFO_WR_PATH.WR_EN;
    endgroup

    //READ
    covergroup cov_rd @(posedge $root.testbench.DUT_U.SLAVE_CLK);
        en : coverpoint `ASFIFO_WR_PATH.RD_EN  iff (`ASFIFO_WR_PATH.RD_RST == 1'b0) {
            bins zero = {0};
            bins one  = {1};
        }

        empty : coverpoint `ASFIFO_WR_PATH.RD_EMPTY iff (`ASFIFO_WR_PATH.RD_RST == 1'b0) {
            bins zero = {0};
            bins one  = {1};
        }

        status : coverpoint `ASFIFO_WR_PATH.RD_STATUS  iff (`ASFIFO_WR_PATH.RD_RST == 1'b0) {
            bins empty   = {0};
            bins aempty  = {[1:`ASFIFO_WR_PATH.ITEMS/2-1]};
            bins afull   = {[`ASFIFO_WR_PATH.ITEMS/2:`ASFIFO_WR_PATH.ITEMS]};
            bins full    = {`ASFIFO_WR_PATH.ITEMS};
        }

        en_status : cross en, status;
    endgroup

    initial begin
       cov_wr wr;
       cov_rd rd;

       wr = new();
       rd = new();
    end
endmodule

//module asfifo_cov_mod #(/*DATA_WIDTH, STATUS_WIDTH,*/ PATH) ();
//
//    //logic CLK_WR;
//    //logic RST_WR;
//    //logic DI;
//    //logic WR;
//    //logic FULL;
//    //logic STATUS;
//
//    //logic CLK_RD;
//    //logic RST_RD;
//    //logic [DATA_WIDTH-1:0] DO;
//    //logic RD;
//    //logic EMPTY;
//
//    //assign CLK_WR = PATH.CLK_WR;
//    //assign RST_WR = PATH.RST_WR;
//    //assign DI     = PATH.DI;
//    //assign WR     = PATH.WR;
//    //assign FULL   = PATH.FULL;
//    //assign STATUS = PATH.STATUS;
//    //
//    //assign CLK_RD = PATH.CLK_RD;
//    //assign RST_RD = PATH.RST_RD;
//    //assign DO     = PATH.DO;
//    //assign RD     = PATH.RD;
//    //assign EMPTY  = PATH.EMPTY;
//
//    covergroup inf @(PATH.MASTER_CLK);
//        test : coverpoint PATH.MASTER_RESET {
//            bins addr[] = {[0:$]};
//        }
//
//    endgroup
//endmodule





//class asfifo  #(PATH);
//
//        //testbench.DUT_U.VHDL_DUT_U.MI_M_ADDR
//
//
//
//        function new();
//            inf = new();
//        endfunction
//
//
//endclass

