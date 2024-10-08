/*
 * file       : program.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: call program in different threads to comunicate with simulation
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


import "DPI-C" function chandle dpi_program_call(string  cmd);
import "DPI-C" function int     dpi_program_wait(chandle prg);


////////////////////////////////////////////////
// CLA
class prog extends uvm_object;
   `uvm_object_utils(uvm_common::prog)

    protected chandle id = null;
    protected int unsigned ret_code;
    protected string       library_path;

    function new(string name = "");
        super.new(name);
        library_path = "";
    endfunction

    function void library_set(string path);
        library_path = path;
    endfunction

    function void pr_call(string prog);
        string cmd;

        if (library_path != "") begin
            cmd = {"export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:", library_path , "; ", prog};
        end else begin
            cmd = {prog};
        end
        id = dpi_program_call(cmd);
    endfunction

    function bit pr_check();
        int ret;
        ret = dpi_program_wait(id);
        if (ret < 0) begin
            return 0;
        end else begin
            ret_code = ret;
            return 1;
        end
    endfunction

    task pr_wait(time wait_time = 1us);
        int ret;
        while ((ret = dpi_program_wait(id)) < 0) begin
            #(wait_time);
        end
        ret_code = ret;
    endtask

    task call(string cmd);
        pr_call(cmd);
        pr_wait();
    endtask

    function int unsigned code_get();
        return ret_code;
    endfunction
endclass
