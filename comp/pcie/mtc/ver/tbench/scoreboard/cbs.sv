/*
 * cbs.sv callbacks from dut interfaces
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

class pcie2miCbs #(MI_WIDTH) extends sv_common_pkg::DriverCbs;
    scoreboard_data #(MI_WIDTH) data;

    function new(scoreboard_data #(MI_WIDTH) data);
        this.data = data;
    endfunction

    virtual task pre_tx(ref sv_common_pkg::Transaction transaction, string inst);
    endtask: pre_tx

    virtual task post_tx(sv_common_pkg::Transaction transaction, string inst);
        data.pcie_request(transaction);
    endtask: post_tx
endclass


class miCbs #(MI_WIDTH) extends sv_common_pkg::MonitorCbs;
    scoreboard_data #(MI_WIDTH) data;

    function new(scoreboard_data #(MI_WIDTH) data);
        this.data = data;
    endfunction

    virtual task pre_rx(ref sv_common_pkg::Transaction transaction, string inst);
    endtask

    virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
        data.mi_proc(transaction);
    endtask
endclass

class mi2pcieCbs #(MI_WIDTH) extends sv_common_pkg::MonitorCbs;
    scoreboard_data #(MI_WIDTH) data;

    function new(scoreboard_data #(MI_WIDTH) data);
        this.data = data;
    endfunction

    virtual task pre_rx(ref sv_common_pkg::Transaction transaction, string inst);
    endtask

    virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
        data.pcie_response(transaction);
    endtask
endclass
