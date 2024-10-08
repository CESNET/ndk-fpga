/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

class MiAgentSlave #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH = 0);

    MiResponder  #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) responder;
    MiMonitor    #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) monitor;


    function new ( string inst, sv_common_pkg::tTransMbx transMbx, virtual iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) mi);
        responder = new({inst, " Driver"}, transMbx, mi);
        monitor   = new({inst, " Monitor"}, mi);
    endfunction

    task setEnabled();
        monitor.setEnabled();
        responder.setEnabled();
    endtask

    task setDisabled();
        responder.setDisabled();
        monitor.setDisabled();
    endtask

endclass
