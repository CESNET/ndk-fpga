/*
 * mvb_speed.sv : Speed meter of Multi-Value bus
 * Author(s): Radek Iša <isa@cesnet.cz>
 * Copyright (C) 2025 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/


class mvb_speed_data;
    int unsigned data;

    function new ();
        this.reset();
    endfunction

    function int unsigned data_get();
        return data;
    endfunction

    function void reset();
        data = 0;
    endfunction

    function void add();
        data += 1;
    endfunction
endclass

class mvb_speed_cbs_rx #(ITEM_WIDTH) extends sv_common_pkg::DriverCbs;

    mvb_speed_data data;

    function new (mvb_speed_data data);
        this.data = data;
    endfunction

    virtual task post_tx(sv_common_pkg::Transaction transaction, string inst);
        MvbTransaction #(ITEM_WIDTH) tr;
        $cast(tr, transaction);

        data.add();
    endtask
endclass

class mvb_speed_cbs_tx #(ITEM_WIDTH) extends sv_common_pkg::MonitorCbs;

    mvb_speed_data data;

    function new (mvb_speed_data data);
        this.data = data;
    endfunction

    virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
        MvbTransaction #(ITEM_WIDTH) tr;
        $cast(tr, transaction);

        data.add();
    endtask
endclass

class mvb_speed #(type T_CBS);

    string inst;
    bit enabled;
    mvb_speed_data data;
    real           speed = 0;
    T_CBS          cbs;
    time delay = 10000ns;

    function new(string inst = "");
        data = new();
        cbs  = new(data);
        this.inst = inst;
    endfunction

    virtual task setEnabled();
        enabled = 1;
        fork
            this.run();
        join_none;
    endtask

    virtual task setDisabled();
        enabled = 0;
    endtask

    virtual task run();
        const int unsigned const_tns_to_mts = (1s/1ns)/1_000_000; //Transactions per ns to M transactions per second
        while(enabled) begin
            #(delay);

            speed = real'(data.data_get())*const_tns_to_mts/(delay/1ns);
            $write("%s speed %4.2f Mts (Mega transaction per seconds)\n", inst, speed);
            data.reset();
        end
    endtask
endclass
