/*
 * my_component.vhd: Description of my component.
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

virtual class ram_base #(ADDR_WIDTH);

    string inst;

    function new(string inst);
        this.inst   = inst;
    endfunction

    pure virtual function logic[ADDR_WIDTH-1:0] malloc(longint unsigned length, logic[ADDR_WIDTH-1:0] alignmask = 64'h0000000000000003);
    pure virtual function void read(logic[ADDR_WIDTH-1:0]  addr, longint unsigned length, inout byte unsigned data[]);
    pure virtual function void write(logic[ADDR_WIDTH-1:0] addr, longint unsigned length,       byte unsigned data[]);
    pure virtual function void free(logic[ADDR_WIDTH-1:0] addr);
endclass

