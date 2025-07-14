// bar.sv: BAR configuration
// Copyright (C) 2025 CESNET z. s. p. o.
// Author:  Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class bar_config extends uvm_object;
    `uvm_object_utils(uvm_pcie::bar_config)

    protected int unsigned  addr2bar_register[logic[64-1:2]];
    protected logic[64-1:2] bar2addr_register[int unsigned];

    function new(string name = "bar_config");
        super.new(name);
    endfunction

    function void register(int unsigned bar, logic [64-1:2] addr_base);
        addr2bar_register[addr_base] = bar;
        bar2addr_register[bar]       = addr_base;
    endfunction

    function void addr2bar(output int unsigned bar, inout logic [64-1:2] addr);
        logic [64-1:2] base = addr;
        if (addr2bar_register.prev(base)) begin
            bar   = addr2bar_register[base];
            addr -= base;
        end else begin
            bar = 0;
        end
    endfunction

    function void bar2addr(inout int unsigned bar, inout logic [64-1:2] addr);
        logic [64-1:2] base = 0;
        if (bar2addr_register.exists(bar)) begin
            base = bar2addr_register[bar];
        end

        addr += base;
    endfunction
endclass


