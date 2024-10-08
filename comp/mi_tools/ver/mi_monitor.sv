/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

  // --------------------------------------------------------------------------
  // -- Mi Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from Mi32
   * interface signals. After a transaction is received it is sent by callback
   * to processing units (typicaly scoreboard). Unit must be enabled by
   * "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call. You can receive your custom transaction by calling
   * "receiveTransaction" function.
   */
class MiMonitor #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH = 0) extends sv_common_pkg::Monitor;
    //wait on write request
    MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) read_request[$];

    // -- Private Class Atributes --
    virtual iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH).monitor    mi;

    // -- Public Class Methods --
    // -- Constructor ---------------------------------------------------------
    // Create monitor object
    function new (string inst, virtual iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH).monitor mi);
        super.new(inst);
        this.mi = mi;
    endfunction

    ///////////////////////////////////////////////////////
    // run task
    virtual task run();
        MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tr;
        while (enabled) begin
            @(mi.monitor_cb);

            if(mi.monitor_cb.ARDY == 1) begin
                sv_common_pkg::Transaction tr_base;
                tr = new();
                $cast(tr_base, tr);
                tr.tr_type = TR_REQUEST;
                foreach(cbs[i]) cbs[i].pre_rx(tr_base, inst);

                tr.meta    = mi.monitor_cb.MWR;
                tr.address = mi.monitor_cb.ADDR;
                tr.be      = mi.monitor_cb.BE;
                tr.data    = mi.monitor_cb.DWR;

                tr.op = OP_NONE;
                if (mi.monitor_cb.WR == 1'b1) begin
                    tr.op = OP_WRITE;
                end

                if (mi.monitor_cb.RD == 1'b1) begin
                    tr.op   = OP_READ;
                    read_request.push_back(tr);
                end
                foreach(cbs[i]) cbs[i].post_rx(tr, inst);
            end

            if (mi.monitor_cb.DRDY == 1) begin
                MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)  tr_rd;
                sv_common_pkg::Transaction tr_base;

                if(read_request.size() == 0) begin
                    $error("%s MI does not have any read request and DUT setup DRDY\n", inst);
                    $stop();
                end

                tr_rd = read_request.pop_front();
                tr_rd.tr_type = TR_RESPONSE;
                $cast(tr_base, tr_rd);
                foreach(cbs[i]) cbs[i].pre_rx(tr_base, inst);
                tr_rd.data = mi.monitor_cb.DRD;
                foreach(cbs[i]) cbs[i].post_rx(tr_base, inst);
            end
        end
    endtask
endclass
