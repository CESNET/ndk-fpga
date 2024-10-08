/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

class delay_en;
    /////////////////////////////////
    // DELAY
    rand integer delay;
    int Low = 0;
    int High = 3;

    constraint cDelays {
        delay inside {[Low:High]};
    }
endclass

class MiResponder #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH = 0) extends sv_common_pkg::Responder;

    local virtual iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH).tb_slave vif;
    sv_common_pkg::tTransMbx transMbx;

    logic rd, wr;
    logic                  data_vld = 0;
    logic [DATA_WIDTH-1:0] data = 'x;
    logic drdy;
    logic ardy;

    int unsigned data_rq = 0;

    /////////////////////////////////
    // ARDY DELAY
    rand delay_en rand_ardy;
    logic         rand_ardy_vld = 0;
    rand delay_en rand_drdy;
    logic         rand_drdy_vld = 0;

    function new(string inst, sv_common_pkg::tTransMbx transMbx, virtual iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH).tb_slave v);
        super.new(inst);
        vif = v;
        this.transMbx = transMbx;
        rand_drdy = new();
        rand_ardy = new();
    endfunction

    task drdy_clear();
        while (enabled) begin
            @(posedge vif.CLK)
            // change ardy timer and valid
            if(rand_ardy.delay == 0) begin
                rand_ardy_vld = 0;
            end else begin
                rand_ardy.delay--;
            end

            //change drdy timer and valid
            if(rand_drdy.delay != 0) begin
                rand_drdy.delay--;
            end

            //if read request and ardy then add request for data
            if (ardy == 1 && rd == 1) begin
                data_rq++;
            end

            // if is set drdy then remove request for data
            // clear all data
            if (drdy == 1) begin
                    data_vld      = 0;
                    data = 'x;
                    rand_drdy_vld = 0;
                    data_rq--;
            end
            drdy = 0;
        end
    endtask

    // synchronisyde is made by wait step. This method relies on not changing signals befor clock event and not too often.
    // More better synchronyzation is by nonblocking assigment when data is to assing after all active task is executed in actual time slots
    // For more info read Systemverilog documentation
    task drdy_set();
        MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tr;
        sv_common_pkg::Transaction tr_get;

        while(enabled) begin
            @(vif.RD, vif.WR, vif.RESET, posedge vif.CLK)
            #(1);
            rd = vif.RD;
            wr = vif.WR;

            ////////////////////////////
            //setup reset
            if (vif.RESET) begin
                rd = 0;
                wr = 0;
                data = 'x;
                data_vld = 0;
                ardy  = 0;
                drdy  = 0;
                data_rq = 0;
            end

            ////////////////////////////
            // SETUP ARDY
            if (rd == 1 || wr == 1) begin
                if(rand_ardy_vld == 0) begin
                    rand_ardy_vld = 1;
                    rand_ardy.randomize();
                end

                if(rand_ardy.delay == 0) begin
                    ardy = '1;
                end else begin
                    ardy = '0;
                end
            end else begin
                ardy = '0;
            end
            vif.ARDY <= ardy;

            //////////////////////////////////
            // SETUP DRDY
            if (((rd == 1 && ardy) || data_rq != 0)) begin
                if (rand_drdy_vld == 0) begin //dont randomize drdy if data is waiting for send
                    rand_drdy.randomize();
                    rand_drdy_vld = 1;
                end

                // download data if required
                if (rand_drdy.delay == 0 && data_vld == 0) begin
                    data_vld  = transMbx.try_get(tr_get);
                    if (data_vld == 1) begin
                        $cast(tr, tr_get);
                        data  = tr.data;
                    end else begin
                        data = 'x;
                    end
                end
                drdy = data_vld;
            end else begin
                drdy = 0;
            end

           // set interface
           vif.DRDY <= drdy;
           vif.DRD  <= data;
       end
   endtask

    ///////////////////////////////////////////
    // RUN TASK
    virtual task run();
        vif.ARDY <= '0;
        vif.DRDY <= '0;
        vif.DRD  <= '0;
        data_rq = 0;
        fork
            drdy_set();
            drdy_clear();
        join
    endtask
endclass

