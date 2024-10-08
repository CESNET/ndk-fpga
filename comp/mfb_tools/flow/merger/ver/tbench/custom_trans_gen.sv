/*
* custom_trans_gen.sv: Custom transaction generator
* Copyright (C) 2018 CESNET z. s. p. o.
* Author(s): Jakub Cabal <cabal@cesnet.cz>
*
* SPDX-License-Identifier: BSD-3-Clause
*/

//import sv_common_pkg::*;
import sv_mvb_pkg::*;
import sv_mfb_pkg::*;
import test_pkg::*;

class CustomTransGenerator;
    string inst;                      // Generator Identifier
    bit enabled;                      // Generator enabled
    bit switch;                      // Generator port
    int cntr;                      // Transaction ID counter
    ScoreboardGeneratorCbs cbs;
    tTransMbx mvbTransMbx;
    tTransMbx mfbTransMbx;

    int unsigned stopAfterTransCount; // Generator will stop after specified number of transactions
    protected int data_id;            // Transaction counter

    Transaction blueprint;

    function new (string inst, int switch);
        this.mvbTransMbx = new(10);
        this.mfbTransMbx = new(10);
        this.inst = inst; // Module name
        this.enabled = 0; // Module is disabled by default
        this.switch = switch;
        this.cntr = 0;
    endfunction

    task setEnabled(int unsigned transCount = 1);
        enabled = 1; // Driver Enabling
        stopAfterTransCount = transCount;
        data_id = 0;
        fork
            run(); // Creating generator subprocess
        join_none; // Don't wait for ending
    endtask

    task setDisabled();
        enabled = 0; // Disable generator
    endtask

    virtual function void setCallbacks(ScoreboardGeneratorCbs cbs);
        this.cbs = cbs;
    endfunction

    task run();
        Transaction tr;
        CustomTransaction #(MVB_ITEM_WIDTH,MFB_ITEM_WIDTH,MFB_META_WIDTH) custom_tr;
        MvbTransaction #(MVB_ITEM_WIDTH) mvb_tr;
        MfbTransaction #(MFB_ITEM_WIDTH,MFB_META_WIDTH) mfb_tr;
        int data_len;

        while (enabled && data_id < stopAfterTransCount)
        begin
            // Copy blueprint
            tr = blueprint.copy();
            // Fill the transaction with random data
            assert(tr.randomize);
            // Cast custom transaction
            $cast(custom_tr,tr);
            custom_tr.switch = switch;
            // Disable payload by parameter
            if (!RX_PAYLOAD_EN[switch])
                 custom_tr.payload = 0;
            // Add payload to HDR
            custom_tr.hdr[4-1 : 0] = custom_tr.payload;
            custom_tr.data[0][4-1 : 0] = custom_tr.payload;
            // Add switch to HDR
            custom_tr.hdr[8-1 : 4] = custom_tr.switch;
            custom_tr.data[0][8-1 : 4] = custom_tr.switch;
            // Add ID number
            if (MFB_ITEM_WIDTH>=16) begin
                if (custom_tr.payload)
                    custom_tr.data[0][16-1 : 8] = cntr;
                else
                    custom_tr.data[0][16-1 : 8] = 0;
            end else if (custom_tr.data.size()>1) begin
                if (custom_tr.payload)
                    custom_tr.data[1][8-1 : 0]  = cntr;
                else
                    custom_tr.data[1][8-1 : 0]  = 0;
            end
            if (MVB_ITEM_WIDTH>=16) begin
                custom_tr.hdr[16-1 : 8] = cntr;
            end
            cntr = cntr+1;
            // send custom transaction to scoreboard
            cbs.post_gen(custom_tr);

            // Create MVB header packet
            mvb_tr = new();
            // add header
            mvb_tr.data = custom_tr.hdr;
            // send mvb transaction to driver
            mvbTransMbx.put(mvb_tr);

            // create MFB data packet
            if (custom_tr.payload) begin
                mfb_tr = new();
                mfb_tr.meta = custom_tr.meta;
                mfb_tr.data = new[custom_tr.data.size()];
                for (int i=0; i < custom_tr.data.size(); i++) begin
                    mfb_tr.data[i] = custom_tr.data[i];
                end
                // send mfb transaction to driver
                mfbTransMbx.put(mfb_tr);
            end

            //$display("MFB TRANSACTION %d SENDING TO DRIVER",data_id);
            data_id = data_id + 1;
        end // while
        enabled = 0;
        //$display("GENERATOR STOP");
    endtask

endclass
