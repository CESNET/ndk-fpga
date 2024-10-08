//-- dut.sv: Design under test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mi_if.dut_slave config_mi
    );

    logic axi_rready;
    logic axi_rvalid;
    logic axi_arvalid;

    logic axi_bready;
    logic axi_bvalid;
    logic axi_wvalid;

    MI2AXI4 #(
    ) VHDL_DUT_U (
        .CLK        (CLK),
        .RESET      (RST),

        .MI_ADDR    (config_mi.ADDR),
        .MI_DWR     (config_mi.DWR),
        .MI_BE      (config_mi.BE),
        .MI_WR      (config_mi.WR),
        .MI_RD      (config_mi.RD),
        .MI_ARDY    (config_mi.ARDY),
        .MI_DRD     (config_mi.DRD),
        .MI_DRDY    (config_mi.DRDY),

        .AXI_AWID    (),
        .AXI_AWADDR  (),
        .AXI_AWLEN   (),
        .AXI_AWSIZE  (),
        .AXI_AWBURST (),
        .AXI_AWPROT  (),
        .AXI_AWVALID (),
        .AXI_AWREADY (1'b1),
        .AXI_WDATA   (),
        .AXI_WSTRB   (),
        .AXI_WVALID  (axi_wvalid),
        .AXI_WREADY  (1'b1),
        .AXI_BID     (8'b0),
        .AXI_BRESP   (2'b0),
        .AXI_BVALID  (axi_bvalid),
        .AXI_BREADY  (axi_bready),
        .AXI_ARID    (),
        .AXI_ARADDR  (),
        .AXI_ARLEN   (),
        .AXI_ARSIZE  (),
        .AXI_ARBURST (),
        .AXI_ARPROT  (),
        .AXI_ARVALID (axi_arvalid),
        .AXI_ARREADY (1'b1),
        .AXI_RID     (8'b0),
        .AXI_RDATA   (64'hffffffffdeadcafe),
        .AXI_RRESP   (2'b0),
        .AXI_RLAST   (1'b1),
        .AXI_RVALID  (axi_rvalid),
        .AXI_RREADY  (axi_rready)
    );


    always @(posedge CLK)
    begin
        if (axi_rready)
            axi_rvalid <= axi_arvalid;
    end

    always @(posedge CLK)
    begin
        if (axi_bready)
            axi_bvalid <= axi_wvalid;
    end

endmodule
