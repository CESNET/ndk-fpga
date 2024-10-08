//-- sync.sv: synchronization classes
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

//sync classes
class sync_id;
    protected int unsigned active_id;
    protected semaphore    sem;
    protected semaphore    check;
    protected int unsigned processes;

    function new();
        active_id = 0;
        sem  = new(1);
        check  = new(1);
    endfunction

    task get_start(int unsigned id);
        // It can continue if it is write to same bank
        check.get();
        if (processes == 0 && active_id != id) begin
            sem.get();
            this.active_id = id;
        end
    endtask

    task get_end();
        this.processes++;
        check.put();
    endtask

    task put_start();
        check.get();
        this.processes--;
        if (this.processes == 0) begin
            sem.put();
        end
    endtask

    task put_end();
        check.put();
    endtask

    task get(int unsigned id);
        get_start(id);
        get_end();
    endtask

    task put();
        put_start();
        put_end();
    endtask
endclass

