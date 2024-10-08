/*
 * mfb_speed.sv : Speed meter of Multi-Frame Bus
 * Author(s): Radek Iša <isa@cesnet.cz>
 *            Daniel Kříž <xkrizd01@vutbr.cz>
 * Copyright (C) 2021 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/


class mfb_speed_data;
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

    function void add(int unsigned size);
        data += size;
    endfunction
endclass

class mfb_speed_cbs_rx #(MFB_ITEM_WIDTH, MFB_META_WIDTH) extends sv_common_pkg::DriverCbs;

    mfb_speed_data data;

    function new (mfb_speed_data data);
        this.data = data;
    endfunction

    virtual task post_tx(sv_common_pkg::Transaction transaction, string inst);
        sv_mfb_pkg::MfbTransaction #(MFB_ITEM_WIDTH, MFB_META_WIDTH) tr;
        $cast(tr, transaction);

        data.add(tr.data.size()*MFB_ITEM_WIDTH);
    endtask
endclass

class mfb_speed_cbs_tx #(MFB_ITEM_WIDTH, MFB_META_WIDTH) extends sv_common_pkg::MonitorCbs;

    mfb_speed_data data;

    function new (mfb_speed_data data);
        this.data = data;
    endfunction

    virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
        sv_mfb_pkg::MfbTransaction #(MFB_ITEM_WIDTH, MFB_META_WIDTH) tr;
        $cast(tr, transaction);

        data.add(tr.data.size()*MFB_ITEM_WIDTH);
    endtask
endclass

class mfb_speed #(type T_CBS);

    string inst;
    bit enabled;
    mfb_speed_data data;
    int unsigned speed = 1; //desing wait on 0 before end. this is just for start.
    T_CBS          cbs;
    int unsigned delay = 10000; //test_pkg::RX_MFB_SPEED_DELAY;

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
        while(enabled) begin
            #(delay*1ns);

            speed = data.data_get()/delay;
            $write("%s speed %d Gbps\n", inst, speed);
            data.reset();
        end
    endtask
endclass
