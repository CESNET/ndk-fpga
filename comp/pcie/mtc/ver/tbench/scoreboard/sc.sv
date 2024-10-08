/*
 * sc.sv scoreboard for mtc component
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

class sc #(MI_WIDTH);

    scoreboard_data #(MI_WIDTH) data;
    pcie2miCbs      #(MI_WIDTH) pcie_cq_cbs;
    mi2pcieCbs      #(MI_WIDTH) pcie_cc_cbs;
    miCbs           #(MI_WIDTH) mi_cbs;

    function new ();
        data = new();
        pcie_cq_cbs = new(data);
        pcie_cc_cbs = new(data);
        mi_cbs      = new(data);
    endfunction

    function void verbose_set(int unsigned level);
        data.verbose_set(level);
    endfunction

    function void display(string prefix = "");
        data.display(prefix);
    endfunction

    task wait_done();
        data.wait_done();
    endtask
endclass

