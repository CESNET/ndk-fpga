//-- mi_common_data_checker.sv: verification component for data checking mi transaction
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>
//--            Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
//--
//-- SPDX-License-Identifier: BSD-3-Clause

// ----------------------------------------------------------------------------
//                        Scoreboard data
// ----------------------------------------------------------------------------
class mi_common_data_checker #(MI_WIDTH, MI_META_WIDTH);
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
