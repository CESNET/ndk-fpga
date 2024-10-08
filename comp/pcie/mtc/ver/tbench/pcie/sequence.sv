/*
 * transaction.sv pcie competition transaction
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

///////////////////////////////////////////////////
// PCIE EXPRESS TRANSACTION SEQUENCE
///////////////////////////////////////////////////
class seq_cfg;
    //max request read size
    int unsigned mrrs = 512;

    rand int unsigned rand_count = 0;

    rand int unsigned data_size_max;
    rand int unsigned data_size_min;

    constraint c1 {
        data_size_min >= 1;
        data_size_max <= mrrs;
        data_size_min <= data_size_max;

        data_size_min dist {[1:4] :/ 20, [5:128] :/ 10, [128:mrrs] :/ 5, mrrs :/ 1};
        data_size_max dist {[1:4] :/ 20, [5:128] :/ 10, [128:mrrs] :/ 5, mrrs :/ 1};

        rand_count    dist {[1:10] :/ 5, [20:100] :/ 40, [128:256] :/ 5 };
    }

    function new (int unsigned mrrs);
        this.mrrs = mrrs;
    endfunction
endclass

class seq extends Transaction;
    seq_cfg cfg;

    function new(seq_cfg cfg);
        this.cfg = cfg;
    endfunction

    /////////////////////////////
    // GENERATE RANDOMIZE OBJECT
    function void pre_randomize();
        if (cfg.rand_count == 0) begin
            assert(cfg.randomize());
        end else begin
            cfg.rand_count--;
        end

        this.data_size_max = cfg.data_size_max;
        this.data_size_min = cfg.data_size_min;
    endfunction


    ////////////////////////////
    // copy function
    virtual function sv_common_pkg::Transaction copy(sv_common_pkg::Transaction to = null);
        seq tr;
        if(to == null) begin
            tr = new(cfg);
        end else begin
            $cast(tr, to);
            tr.cfg = cfg;
        end

        return super.copy(tr);
    endfunction
endclass

