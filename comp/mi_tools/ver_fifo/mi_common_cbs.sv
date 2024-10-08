//-- mi_common_cbs.sv: Callbacks for common mi fifo interface
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>
//--            Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
//--
//-- SPDX-License-Identifier: BSD-3-Clause

`include "mi_common_data_checker.sv"

// ----------------------------------------------------------------------------
//                      Callback classes
// ----------------------------------------------------------------------------
class master_cbs #(MI_WIDTH, MI_META_WIDTH) extends  sv_common_pkg::MonitorCbs;
    mi_common_data_checker #(MI_WIDTH, MI_META_WIDTH) data;

    function new (mi_common_data_checker #(MI_WIDTH, MI_META_WIDTH) data);
        this.data = data;
    endfunction

    virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
        sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH) tr;

        tr = new();
        transaction.copy(tr);
        data.master_send(tr);
    endtask
endclass

class slave_cbs #(MI_WIDTH, MI_META_WIDTH) extends  sv_common_pkg::MonitorCbs;
    mi_common_data_checker #(MI_WIDTH, MI_META_WIDTH) data;

    function new (mi_common_data_checker #(MI_WIDTH, MI_META_WIDTH) data);
        this.data = data;
    endfunction

    virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
        sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH) tr;

        tr = new();
        transaction.copy(tr);
        data.slave_send(tr);
    endtask
endclass
