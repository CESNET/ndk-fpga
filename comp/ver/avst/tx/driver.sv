/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

class driver #(REGIONS) extends sv_common_pkg::Driver;

    ///////////////////////////
    //Variables
    virtual avst_tx_if #(REGIONS).driver vif;
    //config object...
    config_item cfg;
    //actual status in
    // INIT  => just for start
    // RESET => bus is in reset state => delete all data
    // SEND  => driver can send data on bus
    // WAIT  => driver must not send data on bus becouse component is not
    //          cappable receve any data.
    typedef enum {INIT, RESET, SEND, WAIT} status_t;
    status_t status;
    //rdy delay
    bit rdy[$];
    int unsigned read_allowance;
    int unsigned verbosity = 0;

    //////////////////////////
    // functions
    function new(string inst, sv_common_pkg::tTransMbx mbx, virtual avst_tx_if #(REGIONS) vif, config_item cfg = null);
        super.new(inst, mbx);
        this.vif = vif;
        if (cfg != null) begin
            this.cfg = cfg;
        end else begin
            this.cfg = new();
        end
    endfunction

    function void verbosity_set(int unsigned level);
        verbosity = level;
    endfunction

    //////////////////////////
    // function drive signals on avalon rx bus
    task run();
        string s;
        bit act_rdy;
        // setup init state to reset
        status = INIT;

        // drive signals
        forever begin
            ///////////////
            // setup signals after reset
            if (status == RESET) begin
                read_allowance = 0;
                rdy.delete();
                for (int unsigned it = 0; it < cfg.read_latency; it++) begin
                    rdy.push_back(1'b0);
                end
                status = WAIT;
            end

            ///////////////
            // If rdy have beed setup, we can send data
            act_rdy = rdy.pop_front();
            if (act_rdy === 1'b1) begin
                status = SEND;
            end

            ///////////////
            // check if driver has to stop sending data
            // becouse rdy have been enought time deassert
            if(vif.driver_cb.ready === 1'b0) begin
                if (read_allowance == cfg.read_allowance) begin
                    status = WAIT;
                end if (vif.driver_cb.valid !== '0) begin
                    read_allowance++;
                end
            end

            ///////////////
            // this block setup driver
            if (status == SEND) begin
                for (int i = 0; i < REGIONS; i++) begin //two blocks
                   sv_common_pkg::Transaction tr;
                   transaction             req;

                   if(transMbx.try_get(tr) == 1) begin
                       $cast(req, tr);
                       vif.driver_cb.valid[i] <= req.valid;
                       vif.driver_cb.data[(i+1)*256-1  -:256] <= req.data;
                       vif.driver_cb.hdr[(i+1)*128-1   -:128] <= req.hdr;
                       vif.driver_cb.prefix[(i+1)*32-1 -:32]  <= req.prefix;
                       vif.driver_cb.sop[i]                   <= req.sop;
                       vif.driver_cb.eop[i]                   <= req.eop;
                       vif.driver_cb.empty[(i+1)*3-1     -:3] <= req.empty;
                       vif.driver_cb.vf_active[i]             <= req.vf_active;
                       vif.driver_cb.vf_num[(i+1)*10-1 -:10]  <= req.vf_num;
                       vif.driver_cb.bar_range[(i+1)*3-1 -:3] <= req.bar_range;

                       if (verbosity > 4) begin
                            string time_s;
                            $sformat(time_s, "%t", $time());
                            req.display({inst, " RX transaction ", time_s});
                       end
                   end else begin
                       //req = new;
                       //assert(req.randomize());
                       vif.driver_cb.valid[i] <= 1'b0;
                       vif.driver_cb.data[(i+1)*256-1  -:256] <= 'X;
                       vif.driver_cb.hdr[(i+1)*128-1   -:128] <= 'X;
                       vif.driver_cb.prefix[(i+1)*32-1 -:32]  <= 'X;
                       vif.driver_cb.sop[i]                   <= 'X;
                       vif.driver_cb.eop[i]                   <= 'X;
                       vif.driver_cb.empty[(i+1)*3-1     -:3] <= 'X;
                       vif.driver_cb.vf_active[i]             <= 'X;
                       vif.driver_cb.vf_num[(i+1)*10-1 -:10]  <= 'X;
                       vif.driver_cb.bar_range[(i+1)*3-1 -:3] <= 'X;
                   end

                end
            end else if(status != INIT) begin
                vif.driver_cb.valid <= '0;
            end

            //wait for clock
            @(vif.driver_cb);

            ///////////////
            // check bus response
            if(status == INIT) begin
                status = RESET;
            end

            if (vif.driver_cb.ready === 1'b1) begin
                read_allowance = 1;
            end

            rdy.push_back(vif.driver_cb.ready);
            if (vif.driver_cb.RESET == 1) begin
                status = RESET;
            end
         end
    endtask
endclass

