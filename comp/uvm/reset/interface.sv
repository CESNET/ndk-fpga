/*
 * file       : interface.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: RESET interface
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


interface reset_if (input logic CLK);

    wire logic RESET;

    clocking driver_cb @(posedge CLK);
        output RESET;
    endclocking

    clocking monitor_cb @(posedge CLK);
        input RESET;
    endclocking

    modport dut(input RESET);
    modport driver(clocking driver_cb);
    modport monitor(clocking monitor_cb);
endinterface

