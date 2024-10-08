/*
 * file       : sync.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Synchronization object for RESET
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class sync;
    //////////////////////
    // CONNECT AGENT
    virtual function void reset_start(time start_time);
    endfunction

    virtual function void reset_stop(time stop_time);
    endfunction
endclass

class sync_cbs extends sync;
    sync cbs[$];

    function void push_back(sync cbs);
        this.cbs.push_back(cbs);
    endfunction

    //////////////////////
    // CONNECT AGENT
    virtual function void reset_start(time start_time);
       foreach (cbs[it]) begin
            cbs[it].reset_start(start_time);
        end
    endfunction

    virtual function void reset_stop(time stop_time);
       foreach (cbs[it]) begin
            cbs[it].reset_stop(stop_time);
        end
    endfunction
endclass

class sync_register extends sync;
    sync sync_map[string];

    function void set(string name, sync cbs);
        sync_map[name] = cbs;
    endfunction

    function void delete(string name);
        sync_map.delete(name);
    endfunction

    //////////////////////
    // CONNECT AGENT
    virtual function void reset_start(time start_time);
       foreach (sync_map[it]) begin
            sync_map[it].reset_start(start_time);
        end
    endfunction

    virtual function void reset_stop(time stop_time);
       foreach (sync_map[it]) begin
            sync_map[it].reset_stop(stop_time);
        end
    endfunction
endclass

class sync_terminate extends sync;
    time stop_time;
    time start_time;
    logic start_reset = 0;
    logic stop_reset = 0;

    //////////////////////
    // Synchronization taks
    function logic is_reset();
        return start_reset;
    endfunction


    function logic has_been_reset();
        logic ret;
        ret = start_reset;

        if (stop_reset) begin
            start_reset = 0;
            stop_reset = 0;
        end

        return ret;
    endfunction

    //////////////////////
    // CONNECT AGENT
    virtual function void reset_start(time start_time);
        this.start_time = start_time;
        start_reset = 1;
        stop_reset  = 0;
    endfunction

    virtual function void reset_stop(time stop_time);
        this.stop_time = stop_time;
        stop_reset     = 1;
    endfunction
endclass
