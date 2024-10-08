//-- sv_mi_scoreboard_pkg.sv: Scoreboard for common mi fifo verification
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>
//--            Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
//--
//-- SPDX-License-Identifier: BSD-3-Clause

`include "mi_common_cbs.sv"

// ----------------------------------------------------------------------------
//                        Scoreboard
// ----------------------------------------------------------------------------
class scoreboard #(MI_WIDTH, MI_META_WIDTH);
    mi_common_data_checker        #(MI_WIDTH, MI_META_WIDTH) data;
    master_cbs  #(MI_WIDTH, MI_META_WIDTH) master;
    slave_cbs   #(MI_WIDTH, MI_META_WIDTH) slave;

    function new();
        data   = new();
        master = new(data);
        slave  = new(data);
    endfunction

    function void display(string prefix = "");
        if (prefix != "") begin
            $write("----------------------------------------------------------------------------\n");
            $write("-- %s\n", prefix);
            $write("----------------------------------------------------------------------------\n");
        end

        $write("\tRQ COUNTS %d\n\tRS COUNTS %d\n", data.cmp_rq, data.cmp_rs);
        if (data.fifo_rq.size() != 0 || data.fifo_rs.size() != 0 ) begin
            $write("RQ RS STAY IN FIFO\n");
            $write("\tRQ COUNTS %d\n\tRS COUNTS %d\n", data.fifo_rq.size(), data.fifo_rs.size());
        end
    endfunction
endclass
