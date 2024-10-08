/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

package Scoreboard;
    // ----------------------------------------------------------------------------
    //                        Scoreboard data
    // ----------------------------------------------------------------------------
    class Data #(MI_WIDTH, MI_META_WIDTH);
        //request fifo  => master
        sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH) fifo_rq[$];
        int unsigned                         cmp_rq;
        //response fifo => slave
        sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH) fifo_rs[$];
        int unsigned                         cmp_rs;

        function new ();
            cmp_rq = 0;
            cmp_rs = 0;
        endfunction

        function void master_send(sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH) tr);
            if (tr.tr_type == sv_mi_pkg::TR_REQUEST) begin
                fifo_rq.push_back(tr);
            end

            if (tr.tr_type == sv_mi_pkg::TR_RESPONSE) begin
                cmp_rs++;
                cmp(fifo_rs, tr);
            end
        endfunction

        function void slave_send(sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH) tr);
            if (tr.tr_type == sv_mi_pkg::TR_REQUEST) begin
                cmp_rq++;
                cmp(fifo_rq, tr);
            end

            if (tr.tr_type == sv_mi_pkg::TR_RESPONSE) begin
                fifo_rs.push_back(tr);
            end
        endfunction

        function void cmp(ref sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH) expected[$], sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH) get);
            if( expected.size() == 0) begin
                get.display("UNEXPECTED TRANSACTION");
                $stop();
            end else begin
                sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH) exp_tr;
                string diff;

                exp_tr = expected.pop_front();
                if( exp_tr.compare(get, diff) != 1) begin
                    $error("Transaction ERROR:\n");
                    exp_tr.display("EXPECTED TRANSACTION");
                    get.display("GET TRANSACTION");
                end
            end
        endfunction
    endclass

    // ----------------------------------------------------------------------------
    //                      Callback classes
    // ----------------------------------------------------------------------------
    class master_cbs #(MI_WIDTH, MI_META_WIDTH) extends  sv_common_pkg::MonitorCbs;
        Data #(MI_WIDTH, MI_META_WIDTH) data;

        function new (Data #(MI_WIDTH, MI_META_WIDTH) data);
            this.data = data;
        endfunction

        virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
            sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH) tr;

            tr = new();
            transaction.copy(tr);
            data.master_send(tr);
        endtask
    endclass

    class slave_cbs #(MI_WIDTH, MI_META_WIDTH) extends  sv_common_pkg::MonitorCbs;
        Data #(MI_WIDTH, MI_META_WIDTH) data;

        function new (Data #(MI_WIDTH, MI_META_WIDTH) data);
            this.data = data;
        endfunction

        virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
            sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH) tr;

            tr = new();
            transaction.copy(tr);
            data.slave_send(tr);
        endtask
    endclass


    // ----------------------------------------------------------------------------
    //                        Scoreboard
    // ----------------------------------------------------------------------------
    class main #(MI_WIDTH, MI_META_WIDTH);
        Data         #(MI_WIDTH, MI_META_WIDTH) data;
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

endpackage
