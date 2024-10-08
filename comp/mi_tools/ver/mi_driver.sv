/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

// --------------------------------------------------------------------------
// -- Configuration class for MiDriver => configure random delays
// --------------------------------------------------------------------------
class MiDriverRand;
    rand bit enTxDelay;   // Enable/Disable delays between transactions
    // Enable/Disable delays between transaction (weights)
    int txDelayEn_wt             = 1;
    int txDelayDisable_wt        = 3;

    rand integer txDelay; // Delay between transactions
    // Delay between transactions limits
    int txDelayLow          = 0;
    int txDelayHigh         = 3;

    // -- Constrains --
    constraint cDelays {
      enTxDelay dist { 1'b1 := txDelayEn_wt,
                       1'b0 := txDelayDisable_wt
                     };

      txDelay inside {
                      [txDelayLow:txDelayHigh]
                     };
      }
endclass

  // -- Mi Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to Mi
   * interface. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transaction by calling "sendTransaction" function.
   */
class MiDriver #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH = 0) extends sv_common_pkg::Driver;

    // -- Private Class Atributes --
    virtual iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH).tb_master  mi;
    //randomization class
    MiDriverRand  delay;
    op_type_t     tr_type = OP_NONE; //first no wait on ansver
    // -- Public Class Methods --
    logic ardy;
	logic reset;

    // -- Constructor ---------------------------------------------------------
    // Create driver object
    function new ( string inst,
                   sv_common_pkg::tTransMbx transMbx,
                   virtual iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH).tb_master mi
                         );
      super.new(inst, transMbx);
      this.mi          = mi;           // Store pointer interface
      this.delay       = new();
    endfunction

    task sendTransaction();
        sv_common_pkg::Transaction tr_get;
        MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tr = null;

        //wait to reset end
        while (mi.cb_master.RESET) begin
            send_empty_frame();
            @(mi.cb_master);
        end

        //read data from bus
        if (transMbx.try_get(tr_get) == 0) begin
            send_empty_frame();
        end else begin
            busy = 1;
            $cast(tr, tr_get);
            assert(delay.randomize());
            if (delay.enTxDelay) repeat (delay.txDelay) send_empty_frame();

            foreach (cbs[i]) cbs[i].pre_tx(tr_get, inst);

            tr_type = tr.op;
            mi.cb_master.RD   <= (tr_type == OP_READ);
            mi.cb_master.WR   <= (tr_type == OP_WRITE);
            mi.cb_master.DWR  <= tr.data;
            mi.cb_master.MWR  <= tr.meta;
            mi.cb_master.BE   <= tr.be;
            mi.cb_master.ADDR <= tr.address;
            do begin
                @(mi.cb_master);
                ardy  = mi.cb_master.ARDY;
                reset = mi.cb_master.RESET;
            end while (ardy == 0 && tr_type != OP_NONE && !reset && enabled);

            foreach (cbs[i]) cbs[i].post_tx(tr_get, inst);

            busy = 0;
        end
    endtask

    task send_empty_frame();
        mi.cb_master.RD   <= 0;
        mi.cb_master.WR   <= 0;
        mi.cb_master.DWR  <= 'X;
        mi.cb_master.MWR  <= 'X;
        mi.cb_master.BE   <= 'X;
        mi.cb_master.ADDR <= 'X;
        @(mi.cb_master);
    endtask

    task run();
        while (enabled) begin
            //init
            mi.cb_master.RD <= 0;
            mi.cb_master.WR <= 0;
            //sendt transactions
            forever begin
                sendTransaction();
            end
        end
    endtask
endclass
