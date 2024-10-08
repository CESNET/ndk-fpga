/*
 * file       : interface.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: mi interface
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef MI_INTERFACE
`define MI_INTERFACE


interface mi_if #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) (input logic CLK);

    //COMMON INTERFACE
    wire logic [ADDR_WIDTH-1:0] ADDR;
    wire logic [DATA_WIDTH/8-1:0] BE;
    //WRITE INTERFEC
    wire logic WR;
    wire logic [DATA_WIDTH-1:0] DWR;
    wire logic [META_WIDTH-1:0] META;
    //READ INTERFACE
    wire logic RD;
    wire logic [DATA_WIDTH-1:0] DRD;
    //ACCEPTING INTERFACE
    wire logic ARDY;
    wire logic DRDY;


    clocking cb_master @(posedge CLK);
        input ADDR, BE, WR, DWR, META, RD;
        output DRD, ARDY, DRDY;
    endclocking

    clocking cb_slave @(posedge CLK);
        output ADDR, BE, WR, DWR, META, RD;
        input DRD, ARDY, DRDY;
    endclocking

    clocking monitor_cb @(posedge CLK);
        input ADDR, BE, WR, DWR, META, RD, DRD, ARDY, DRDY;
    endclocking

    modport dut_slave(input ADDR, BE, WR, DWR, META, RD, output DRD, ARDY, DRDY);
    modport dut_master(output ADDR, BE, WR, DWR, META, RD, input DRD, ARDY, DRDY);

    modport tb_master(clocking cb_master);
    modport tb_slave(clocking cb_slave);
    modport monitor(clocking monitor_cb);
endinterface

`endif

