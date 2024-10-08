/*
 * Copyright (C) 2021 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

class pcie_monitor_cbs extends sv_common_pkg::MonitorCbs;

    sv_common_pkg::tTransMbx  mbx_response;


     function new ();
        mbx_response = new();
     endfunction

    task get(output sv_common_pkg::Transaction transaction);
        mbx_response.get(transaction);
    endtask

    virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
        mbx_response.put(transaction.copy());
    endtask
endclass


class pcie_driver_cbs extends sv_common_pkg::DriverCbs;
    sv_common_pkg::tTransMbx mbx_response;

    function new(int unsigned mbx_size = 0);
        mbx_response = new(mbx_size);
    endfunction

    task get(output sv_common_pkg::Transaction transaction);
        mbx_response.get(transaction);
    endtask

    virtual task pre_tx(ref sv_common_pkg::Transaction transaction, string inst);
    endtask

    virtual task post_tx(sv_common_pkg::Transaction transaction, string inst);
        mbx_response.put(transaction.copy());
    endtask
endclass

