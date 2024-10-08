/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

// ----------------------------------------------------------------------------
//                RAND DELAY MI DRIVER
// ----------------------------------------------------------------------------
// configuration class
class rand_mi_driver_delay_cfg;
    rand int rand_count = 0;

    rand int txDelayEn_wt;
    rand int txDelayDisable_wt;

    rand int txDelayLow;
    rand int txDelayHigh;

    constraint c1{
       rand_count inside {[20:100]};
       //delay enabled
       txDelayEn_wt       inside {[0:10]};
       txDelayDisable_wt  inside {[0:40]};
       (txDelayEn_wt != 0) || (txDelayDisable_wt != 0);
       //delay long
       txDelayLow <= txDelayHigh;
       txDelayLow  dist {[0:3] :/ 80, [3:10] :/ 10, [10:20] :/ 5, [50:100] :/ 1};
       txDelayHigh dist {[0:3] :/ 80, [3:10] :/ 10, [10:20] :/ 5, [50:100] :/ 1};
    };
endclass

//randomization class
class rand_mi_driver_delay extends sv_mi_pkg::MiDriverRand;
    rand_mi_driver_delay_cfg cfg;

    function new();
        cfg = new();
    endfunction

    function void pre_randomize ();
        if(cfg.rand_count == 0) begin
            assert(cfg.randomize());
        end

        //setup randomization
        this.txDelayEn_wt      = cfg.txDelayEn_wt;
        this.txDelayDisable_wt = cfg.txDelayDisable_wt;
        this.txDelayLow        = cfg.txDelayLow;
        this.txDelayHigh       = cfg.txDelayHigh;

        //decrement count
        cfg.rand_count--;
    endfunction
endclass

// ----------------------------------------------------------------------------
//                RAND DELAY MI RESPONDER
// ----------------------------------------------------------------------------
// configuration class
class rand_mi_responder_delay_cfg;
    rand int rand_count = 0;
    rand int High;
    rand int Low;

    constraint c1{
       rand_count inside {[20:100]};
       Low <= High;
       Low  dist {[0:3] :/ 80, [3:10] :/ 10, [10:20] :/ 5, [50:100] :/ 1};
       High dist {[0:3] :/ 80, [3:10] :/ 10, [10:20] :/ 5, [50:100] :/ 1};
    }
endclass

// Randomization class
class rand_mi_responder_delay extends sv_mi_pkg::delay_en;
    rand_mi_responder_delay_cfg cfg;

    function new();
        cfg = new();
    endfunction

    function void pre_randomize ();
        if(cfg.rand_count == 0) begin
            assert(cfg.randomize());
        end

        //setup randomization
        this.Low  = cfg.Low;
        this.High = cfg.High;
        //decrement count
        cfg.rand_count--;
    endfunction
endclass

// ----------------------------------------------------------------------------
//               MI TRANSACTION GENERATOR
// ----------------------------------------------------------------------------
//configuration class
class mi_transaction_config #(DATA_WIDTH, ADDR_WIDTH = DATA_WIDTH);
    //sequence length
    rand int unsigned rand_count = 0;

    //rand addres
    rand logic [ADDR_WIDTH-1:0] maxAddr;
    rand logic [ADDR_WIDTH-1:0] minAddr;
    //rand operation
    rand int unsigned distRead;
    rand int unsigned distWrite;
    rand int unsigned distNone;

    constraint c1 {
       //length of sequence
       rand_count inside {[20:200]};
       //address constraint
       minAddr <= maxAddr;
       minAddr % (DATA_WIDTH/8) == 0;
       maxAddr % (DATA_WIDTH/8) == 0;
       //rand distribution between operation
       distRead  inside {[0:40]};
       distWrite inside {[0:40]};
       distNone  inside {[0:10]};
       (distRead != 0) || (distWrite != 0) || (distNone != 0);
    };
endclass

// Randomization class (Transaction)
class mi_sequence #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH = 0) extends sv_mi_pkg::MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH);
    mi_transaction_config #(DATA_WIDTH, ADDR_WIDTH) cfg;

    constraint c2 {
        be dist {DATA_WIDTH > 8 -> (DATA_WIDTH/8)-1 := 7, [0:(DATA_WIDTH/8)-1] := 3};
    };

    function new(mi_transaction_config #(DATA_WIDTH, ADDR_WIDTH) cfg = null);
        if(cfg == null) begin
            this.cfg = new();
        end else begin
            this.cfg = cfg;
        end
    endfunction

    ////////////////////////////
    // set randomization
    function void pre_randomize ();
        if(cfg.rand_count == 0) begin
            assert(cfg.randomize());
        end

        //setup transaction
        this.maxAddress = cfg.maxAddr;
        this.minAddress = cfg.minAddr;
        this.distRead   = cfg.distRead;
        this.distWrite  = cfg.distWrite;
        this.distNone   = cfg.distNone;
        //decrement count
        cfg.rand_count--;
    endfunction

    ////////////////////////////
    // copy function
    virtual function sv_common_pkg::Transaction copy(sv_common_pkg::Transaction to = null);
        mi_sequence #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tr;
        if(to == null) begin
            tr = new(cfg);
        end else begin
            $cast(tr, to);
            tr.cfg = cfg;
        end
        super.copy(tr);

        return tr;
    endfunction
endclass

