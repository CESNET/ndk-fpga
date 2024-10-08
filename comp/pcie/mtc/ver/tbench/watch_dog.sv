/*
 * test.sv mtc verification enviromet
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */


class watch_dog_pcie_cbs extends sv_common_pkg::DriverCbs;
    int unsigned trans_num = 0;

    virtual task pre_tx(ref sv_common_pkg::Transaction transaction, string inst);
    endtask

    virtual task post_tx(sv_common_pkg::Transaction transaction, string inst);
        trans_num++;
    endtask
endclass

class watch_dog_mi_cbs extends sv_common_pkg::MonitorCbs;
    int unsigned trans_num = 0;

    virtual task pre_rx(ref sv_common_pkg::Transaction transaction, string inst);
    endtask

    virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
        trans_num++;
    endtask
endclass



class watch_dog;
    bit  enabled;
    time watch_time;
    watch_dog_pcie_cbs pcie_cbs;
    watch_dog_mi_cbs   mi_cbs;

    function new(time watch_time);
        this.watch_time = watch_time;
        this.pcie_cbs = new();
        this.mi_cbs = new();
    endfunction

    task run();
        int unsigned last_pcie_val = 0;
        int unsigned last_mi_val   = 0;

        while(enabled) begin
            int unsigned new_pcie_val;
            int unsigned new_mi_val;

            #(watch_time);
            new_pcie_val = pcie_cbs.trans_num;
            new_mi_val   = mi_cbs.trans_num;
            if(last_pcie_val >= new_pcie_val && last_mi_val >= new_mi_val) begin
                $timeformat(-9,3,"ns",5);
                $error("DUT probubly is stucked\nDUT haven't recived transaction for %t\n", watch_time);
                $stop();
            end
            last_pcie_val = new_pcie_val;
            last_mi_val   = new_mi_val;
        end
    endtask

    task setEnabled();
        enabled = 1'b1;
        fork
            run();
        join_none
    endtask

    task setDisabled();
        enabled = 1'b0;
    endtask
endclass


