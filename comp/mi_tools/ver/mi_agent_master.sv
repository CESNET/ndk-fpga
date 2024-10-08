/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

class MiAgentMaster #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH = 0);

    MiDriver  #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) driver;
    MiMonitor #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) monitor;


    function new ( string inst, sv_common_pkg::tTransMbx transMbx, virtual iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) mi);
        driver  = new({inst, " Driver"}, transMbx, mi);
        monitor = new({inst, " Monitor"}, mi);
    endfunction

    task setEnabled();
        monitor.setEnabled();
        driver.setEnabled();
    endtask

    task setDisabled();
        driver.setDisabled();
        monitor.setDisabled();
    endtask

endclass
