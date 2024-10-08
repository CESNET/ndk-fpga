/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */


class MiCover #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH = 0);
    string inst;
    virtual iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) vif;

    covergroup cov_mi (int max_rq) @(vif.monitor_cb);

        ///////////////////////////
        //sequence of ARDY, DRDY
        ardy : coverpoint vif.ARDY {
            bins short  = (0 => 1 => 0);
            bins longer = (0 => 1[*2:4]  => 0);
            bins long   = (0 => 1[*5:10] => 0);
            bins max    = (0 => 1[*max_rq]);
            option.at_least = 4;
        }

        drdy : coverpoint vif.DRDY {
            bins short  = (0 => 1 => 0);
            bins longer = (0 => 1[*2:4]  => 0);
            bins long   = (0 => 1[*5:10] => 0);
            bins max    = (0 => 1[*max_rq]);
            option.at_least = 4;
        }

        ///////////////////////////
        //sequence of quit read
        read_sequence : coverpoint vif.RD & vif.ARDY {
            bins short  = (0 => 1 => 0);
            bins longer = (0 => 1[*2:4]    => 0);
            bins long   = (0 => 1[*5:10]   => 0);
            bins max    = (0 => 1[*max_rq]);
            option.at_least = 4;
        }

        write_sequence : coverpoint vif.RD & vif.ARDY & vif.DRDY {
            bins short  = (0 => 1 => 0);
            bins longer = (0 => 1[*2:4]    => 0);
            bins long   = (0 => 1[*5:10]   => 0);
            bins max    = (0 => 1[*max_rq]);
            option.at_least = 4;
        }

        //cross_cov : cross vif.ARDY, drdy;
    endgroup

    function new (string inst, virtual iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH).monitor mi, int max_rq);
        this.vif    = mi;
        this.inst   = inst;
        this.cov_mi = new(max_rq);
    endfunction

    function void display();
        $write("%s \tcoverage %f\n", inst, cov_mi.get_inst_coverage());
    endfunction
endclass

